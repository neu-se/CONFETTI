package edu.berkeley.cs.jqf.fuzz.central;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;
import edu.gmu.swe.knarr.runtime.Coverage;
import edu.gmu.swe.knarr.server.ConstraintOptionGenerator;
import edu.gmu.swe.knarr.server.HashMapStateStore;
import edu.gmu.swe.knarr.server.StateStore;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.service.canonizer.ModelCanonizerService;
import za.ac.sun.cs.green.service.factorizer.ModelFactorizerService;
import za.ac.sun.cs.green.service.z3.ModelZ3JavaService;
import za.ac.sun.cs.green.service.z3.Z3JavaTranslator;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.NotSatException;

import java.io.*;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.atomic.AtomicReference;
import java.util.stream.Collectors;

public class Z3Worker {
    private Data data;

    private static final File Z3_OUTPUT_DIR;

    static {
        String z3Dir = System.getProperty("Z3_OUTPUT_DIR");
        if (z3Dir != null) {
            File f = new File(z3Dir);
            if (!f.exists())
                f.mkdirs();

            if (!f.isDirectory())
                throw new Error("Path " + f + " is not a directory");

            Z3_OUTPUT_DIR = f;
        } else {
            Z3_OUTPUT_DIR = null;
        }
    }

    public Z3Worker(ZestWorker zest, KnarrWorker knarr, String[] filter) {
        data = new Data();
        data.green = new Green();
        Properties props = new Properties();
        props.setProperty("green.services", "model");
        props.setProperty("green.service.model", "(slice (canonize z3))");
        props.setProperty("green.service.model.slice", "za.ac.sun.cs.green.service.slicer.SATSlicerService");
        props.setProperty("green.service.model.canonize", "za.ac.sun.cs.green.service.canonizer.ModelCanonizerService");
        props.setProperty("green.service.model.z3", "za.ac.sun.cs.green.service.z3.ModelZ3JavaService");
        // props.setProperty("green.store",
        // "za.ac.sun.cs.green.store.redis.RedisStore");
        Configuration config = new Configuration(data.green, props);
        config.configure();
        data.slicer = new ModelFactorizerService(data.green);
        data.canonizer = new ModelCanonizerService(data.green);
        data.variableMap = new HashMap<Variable, Variable>();
        data.modeler = new ModelZ3JavaService(data.green, null);
        data.stateStore = new HashMapStateStore();
        data.optionGenerator = new ConstraintOptionGenerator();
    }

    private boolean isTargetFeasible(Target t) {
        Map<String, Expression> res = new HashMap<>();

        boolean found = false;
        for (Expression e : t.constraints) {
            res.put("c" + res.size(), e);
            if (e.metadata != null && e.metadata instanceof Coverage.BranchData) {
                Coverage.BranchData data = (Coverage.BranchData) e.metadata;
                if (data.takenCode == t.branch.takenID && data.notTakenCode == t.branch.notTakenID) {
                    found = true;
                    break;
                }
            }
        }

        // We couldn't find the target constraint
        if (!found)
            return false;

        ArrayList<AbstractMap.SimpleEntry<String, Object>> sat = new ArrayList<>();
        HashSet<String> unsat = new HashSet<>();

        solve(res, sat, unsat);

        return (unsat.isEmpty());
    }

    private byte[] solutionToInput(ArrayList<AbstractMap.SimpleEntry<String, Object>> sat, Map<String, byte[]> funcs) {
        // Get size of solution
        int size = 0;
        for (AbstractMap.SimpleEntry<String, Object> e : sat) {
            if (e.getKey().startsWith("autoVar_")) {
                try {
                    int n = Integer.parseInt(e.getKey().replace("autoVar_", ""));
                    size = Math.max(size, n);
                } catch (NumberFormatException ex) {
                    continue;
                }
            }
        }

        // Copy bytes from solution
        byte ret[] = new byte[size+1];
        for (AbstractMap.SimpleEntry<String, Object> e : sat) {
            if (e.getKey().startsWith("autoVar_")) {
                try {
                    int n = Integer.parseInt(e.getKey().replace("autoVar_", ""));
                    ret[n] = ((Integer) e.getValue()).byteValue();
                } catch (NumberFormatException ex) {
                    continue;
                }
            }
        }

        // Handle solutions to generator functions
        sat.stream().filter(entry -> entry.getKey().startsWith("gen"))
                .forEach(entry -> funcs.put(entry.getKey(), intArrToByteArr((int[])entry.getValue())));

        return ret;
    }

    private static byte[] intArrToByteArr(int[] arr) {
        byte[] ret = new byte[arr.length];
        // This is slow, surely there's a better way...
        for (int i = 0 ; i < ret.length ; i++)
            ret[i] = (byte) arr[i];

        return ret;
    }

    private Optional<Coordinator.Input> negateConstraint(Target t, Set<Expression> hints) {

        Map<String, Expression> res = new HashMap<>();

        Expression targetConstraint = null;

//        for (Expression e : hints)
//            res.put("c" + res.size(), e);

        for (Expression e : t.constraints) {
            if (e.metadata != null && e.metadata instanceof Coverage.BranchData) {
                Coverage.BranchData data = (Coverage.BranchData) e.metadata;
                if (data.takenCode == t.branch.takenID && data.notTakenCode == t.branch.notTakenID) {
                    targetConstraint = e;
                    break;
                }
            } else {
                res.put("c" + res.size(), e);
            }
        }

        if (targetConstraint == null)
            throw new IllegalStateException();

        // Negate the target constraint
        Expression negatedTargetConstraint = new Operation(Operation.Operator.NOT, targetConstraint);

        // Try to solve it
        res.put("c" + res.size(), negatedTargetConstraint);
        ArrayList<AbstractMap.SimpleEntry<String, Object>> sat = new ArrayList<>();
        HashSet<String> unsat = new HashSet<>();
        solve(res, sat, unsat);

        if (unsat.isEmpty()) {
            // Solution found, generate input
            HashMap<String, byte[]> genFuncs = new HashMap<>();
            Coordinator.Input ret = new Coordinator.Input();
            ret.bytes = solutionToInput(sat, genFuncs);
            ret.hints = generatorsToHints(res.values(), genFuncs);
            return Optional.of(ret);
        } else {
            if (unsat.size() == 1) {
                // Try to fix single UNSAT expression

                // Remove UNSAT expression
                Expression ex = res.remove(unsat.stream().findFirst().get());

                // Maybe it's a String.equals without enough size?
                Optional<Coordinator.Input> sol = replaceEqualsByStartsWith(res, ex);

                // Put the expression back
                res.put(unsat.stream().findFirst().get(), ex);

                // Did this work?
                if (sol.isPresent())
                    return sol;
            }
            if (!hints.isEmpty())
                return negateConstraint(t, new HashSet<>());
            return Optional.empty();
        }
    }

    public static LinkedList<Coordinator.StringHint[]> generatorsToHints(Collection<Expression> exps, Map<String, byte[]> genFuncs) {
        LinkedList<Coordinator.StringHint[]> ret = new LinkedList<>();

        HashMap<Integer, Set<String>> hints = new HashMap<>();

        // Luís:  I'm sure this code can be optimized
        for (Map.Entry<String, byte[]> entry : genFuncs.entrySet()) {
            for (Expression ex : exps) {
                try {
                    ex.accept(new Visitor() {
                        @Override
                        public void postVisit(FunctionCall function) throws VisitorException {
                            if (function.getName().equals(entry.getKey())) {
                                for (Expression arg : function.getArguments()) {
                                    arg.accept(new Visitor() {
                                        @Override
                                        public void postVisit(BVVariable variable) throws VisitorException {
                                            if (variable.getName().startsWith("autoVar_")) {
                                                int idx = Integer.parseInt(variable.getName().replace("autoVar_", ""));
                                                Set<String> hs = hints.get(idx);
                                                if (hs == null) {
                                                    hs = new HashSet<>();
                                                    hints.put(idx, hs);
                                                }
                                                hs.add(new String(entry.getValue()));
                                            }
                                        }
                                    });
                                }
                            }
                        }
                    });
                } catch (VisitorException e) {
                    e.printStackTrace();
                    continue;
                }
            }
        }

        for (int i = 0 ; !hints.isEmpty() ; i++) {
            Set<String> strings = hints.remove(i);
            Coordinator.StringHint[] empty = new Coordinator.StringHint[0];
            if (strings == null) {
                ret.addLast(empty);
            } else {
                ret.addLast(strings.stream()
                        .map(s -> new Coordinator.StringHint(s, Coordinator.HintType.Z3))
                        .collect(Collectors.toList())
                        .toArray(empty));
            }
        }

        return ret;
    }

    private Set<Expression> hintsToConstraints(List<Expression> constraints, HashMap<Integer, HashSet<Coordinator.StringHint>> hints) {
        HashSet<Expression> ret = new HashSet<>();
        HashMap<String, FunctionCall> calls = new HashMap<>();

        if (hints == null || hints.isEmpty())
            return new HashSet<>();


        // Find generator functions and arguments
        for (Expression c : constraints) {
            try {
                c.accept(new Visitor() {
                    @Override
                    public void postVisit(FunctionCall function) throws VisitorException {
                        if (function.getName().startsWith("gen"))
                            // TODO ensure same arguments on collisions
                            calls.put(function.getName(), function);
                    }
                });
            } catch (VisitorException e) {
                throw new Error(e);
            }
        }

        for (Map.Entry<String, FunctionCall> entry : calls.entrySet()) {
            // Match arguments with hints
            HashSet<Integer> bytes = new HashSet<>();
            for (Expression arg : entry.getValue().getArguments()) {
                try {
                    arg.accept(new Visitor() {
                        @Override
                        public void postVisit(BVVariable variable) throws VisitorException {
                            if (variable.getName().startsWith("autoVar_")) {
                                bytes.add(Integer.parseInt(variable.getName().replace("autoVar_", "")));
                            }
                        }
                    });
                } catch (VisitorException e) {
                    throw new Error(e);
                }
            }

            // Generate constraints based on hints
            Expression hintsConstraint = new BoolConstant(false);
            boolean foundHints = false;
            for (int i : bytes) {
                HashSet<Coordinator.StringHint> hs = hints.get(i);
                if (hs != null) {
                    for (Coordinator.StringHint h : hs) {
                        foundHints = true;
                        // funcHint goes char by char stating that they are ==
                        Expression funcHint = new BoolConstant(true);
                        for (int j = 0 ; j < h.hint.length() ; j++) {
                            Expression[] args = new Expression[2];
                            args[0] = new IntConstant(j);
                            args[1] = entry.getValue().getArguments()[1];
                            funcHint = new Operation(
                                    Operation.Operator.AND,
                                    funcHint,
                                    new Operation(
                                            Operation.Operator.EQ,
                                            new FunctionCall(
                                                    entry.getValue().getName(),
                                                    args
                                            ),
                                            new IntConstant(h.hint.charAt(j))
                                    )
                            );
                        }
                        hintsConstraint = new Operation(Operation.Operator.OR, hintsConstraint, funcHint);
                    }
                }
            }

            if (foundHints)
                ret.add(hintsConstraint);
        }

        return ret;
    }

    public Optional<Coordinator.Input> exploreTarget(Target t) {
        // Set timeout
        {
            String to;
            if ((to = System.getProperty("Z3_TIMEOUT")) != null)
                Z3JavaTranslator.timeoutMS = Integer.parseInt(to);
            else
                Z3JavaTranslator.timeoutMS = 3600 * 1000; // 1h
        }

        try {

//            if (!isTargetFeasible(t)) {
//                // TODO tell the coordinator that this target is not feasible
//                return Optional.empty();
//            }

            Set<Expression> stringHintConstraints = hintsToConstraints(t.constraints, t.hints);
            Optional<Coordinator.Input> input = negateConstraint(t, stringHintConstraints);
            return input;

        } catch (Z3Exception | ClassCastException e) {
            System.err.println(e.getMessage());
            e.printStackTrace();
        } catch (Throwable e) {
            System.err.println(e.getMessage());
            e.printStackTrace();
        }

        return Optional.empty();
    }

//        LinkedList<Expression> csToSolve = new LinkedList<>();
//            Map<String, Expression> res = new HashMap<>();
//
//            for (Expression e : t.constraints) {
//                csToSolve.add(e);
//                res.put("c" + res.size(), e);
//                if (e.metadata != null && e.metadata instanceof Coverage.BranchData) {
//                    Coverage.BranchData data = (Coverage.BranchData) e.metadata;
//                    if (data.takenCode == t.branch.takenID && data.notTakenCode == t.branch.notTakenID)
//                        break;
//                }
//            }
//
//            ArrayList<AbstractMap.SimpleEntry<String, Object>> sat = new ArrayList<>();
//            HashSet<String> unsat = new HashSet<>();
//
//            sat.clear();
//            unsat.clear();
//
//            try {
//                solve(res, sat, unsat);
//
//                for (String s : unsat)
//                    System.out.println(res.get(s));
//
//                if (unsat.isEmpty()) {
//                    // Try negating constraints of branches
//                    res.clear();
//                    for (Expression cs : csToSolve) {
//                        sat.clear();
//                        unsat.clear();
//                        if (cs.metadata instanceof Coverage.BranchData) {
//                            Coverage.BranchData data = (Coverage.BranchData) cs.metadata;
//                            res.put("c" + res.size(), new Operation(Operation.Operator.NOT, cs));
//                            solve(res, sat, unsat);
//
//                            if (Z3_OUTPUT_DIR != null)
//                                dumpToTXTFile(Paths.get(Z3_OUTPUT_DIR.getAbsolutePath(), "constraints" + solved + ".txt").toFile(), res);
//
//                            res.remove("c" + (res.size() - 1));
//
//                            if (!unsat.isEmpty()) {
//                                // Unsat, try different things to make it SAT
//
//                                // Is it UNSAT because of a String.equals?
//                                // Maybe it's because the lengths don't match perfectly
//                                // Turn that into startsWith
//                                LinkedList<Coordinator.StringHint> hints = new LinkedList<>();
//                                byte[] sol = replaceEqualsByStartsWith(res, cs, hints);
//                                if (sol != null) {
//                                    // Give solution and hint to JQF
//                                    HashSet<Integer> bytes = new HashSet<>();
//                                    KnarrWorker.findControllingBytes(cs, bytes, new HashSet<>());
//                                    for (Coordinator.StringHint hint : hints)
//                                        System.out.println("Equals hint: " + hint.getHint() + " on bytes " + bytes);
//                                    Coordinator.Input input = new Coordinator.Input();
//                                    input.bytes = new byte[t.input.length * 2];
//                                    System.arraycopy(sol, 0, input.bytes, 0, Math.min(sol.length, t.input.length));
//                                    if (t.input.length * 2 > sol.length) {
//                                        System.arraycopy(t.input, sol.length, input.bytes, sol.length, t.input.length - sol.length);
//                                        System.arraycopy(t.input, 0, input.bytes, t.input.length, t.input.length);
//                                    }
//                                    input.hints = new LinkedList<>();
//                                    Coordinator.StringHint[] empty = new Coordinator.StringHint[0];
//                                    for (int i = 0; i < t.input.length; i++)
//                                        input.hints.add(bytes.contains(i) ? hints.toArray(empty) : empty);
//
//                                    // Send input to knarr, check if we explore target
//                                    LinkedList<Expression> updatedConstraints = knarr.getConstraints(input.bytes, input.hints);
//                                    List<Expression> lst = updatedConstraints.stream().filter(e -> e.metadata != null).collect(Collectors.toList());
//                                    zest.addInputFromZ3(input);
//                                } else if ((sol = handleStringLength(res, cs, hints)) != null) {
//                                    // Give hint to JQF
//                                    System.out.println("String length hint: " + hints);
//                                } else {
//                                    // Failed, stop trying
//                                    for (String s : unsat)
//                                        System.out.println(res.get(s));
//                                }
//                            } // TODO It was SAT, generate input and send it to Zest
//                        } else {
//                            // Constraints were SAT, generate hint
//                        }
//                    }
//                }
//            } catch (Z3Exception | ClassCastException e) {
//                System.err.println(e.getMessage());
//                e.printStackTrace();
//            } catch (Throwable e) {
//                System.err.println(e.getMessage());
//                e.printStackTrace();
//            }
//
//
//            continue;
//        }

    private byte[] handleStringLength(Map<String, Expression> res, Expression cs, LinkedList<Coordinator.StringHint> hints) {
        // Check if the constraint is LENGTH

        if (!(cs instanceof Operation && ((Operation)cs).getOperand(1) instanceof Operation))
            return null;

        Operation comparison = (Operation) cs;
        Operation i2bv = (Operation) comparison.getOperand(1);

        if (i2bv.getOperator() != Operation.Operator.I2BV || !(i2bv.getOperand(0) instanceof Operation))
            return null;

        Operation length = (Operation) i2bv.getOperand(0);

        if (length.getOperator() != Operation.Operator.LENGTH)
            return null;

        // Is is a LENGTH constraint

        // 1st figure out what length are we looking for
        BVVariable bv = new BVVariable("expectedLength", 32);

        res.put("expectedLength", new Operation(Operation.Operator.EQUALS, new Operation(Operation.Operator.I2BV, 32, comparison.getOperand(0)), bv));

        ArrayList<AbstractMap.SimpleEntry<String, Object>> sat = new ArrayList<>();
        HashSet<String> unsat = new HashSet<>();
        solve(res, sat, unsat);

        res.remove("expectedLength");

        if (!unsat.isEmpty()) {
            // No good, didn't work
            res.remove("c" + (res.size()-1));
            return null;
        }

        int expectedLength = -1;

        for (AbstractMap.SimpleEntry<String, Object> e : sat) {
            if (e.getKey().equals("expectedLength")) {
                expectedLength = (int) e.getValue();
                break;
            }
        }

        // Something went wrong
        if (expectedLength == -1) {
            return null;
        }

        // 2nd add/remove characters from the generated string

        // Find string var
        int actualLength = 0;
        Expression concat = length.getOperand(0);
        while (concat instanceof Operation) {
            actualLength += 1;
            concat = ((Operation) concat).getOperand(0);
        }

        StringVariable generatedString;
        if (concat instanceof StringVariable)
            generatedString = (StringVariable) concat;
        else
            return null;

        // Find generator function
        Expression f = ((Operation)length.getOperand(0)).getOperand(1);
        while (f instanceof Operation) {
            f = ((Operation) f).getOperand(0);
        }

        FunctionCall gen;
        if (f instanceof FunctionCall)
            gen = (FunctionCall)f;
        else
            return null;

        // Find the solution for the function
        int[] genSol = null;
        for (AbstractMap.SimpleEntry<String, Object> e : sat) {
            if (e.getKey().equals(gen.getName())) {
                genSol = (int[]) e.getValue();
                break;
            }
        }

        if (genSol == null)
            return null;

        // We are trying to negate this constraint, so generate a suitable hint
        Operation.Operator op = comparison.getOperator();

        if (op == Operation.Operator.NE) {
            // Hint must be the same as expected length
            if (expectedLength == actualLength)
                return null;

            if (expectedLength < actualLength) {
                // Add characters
                op = Operation.Operator.LT;
            } else {
                // Remove characters
                op = Operation.Operator.GT;
            }
        }

        switch (op) {
            case GE:
            case GT: {
                // Hint must be smaller than expected length
                if (expectedLength - 1 > genSol.length)
                    return null;
                byte[] hint = new byte[expectedLength - 1];
                for (int i = 0 ; i < hint.length ; i++)
                    hint[i] = (byte) genSol[i]; // Different types, cannot arrayCopy
                hints.add(new Coordinator.StringHint(new String(hint), Coordinator.HintType.Z3));
                // TODO
                return new byte[0];
            }
            case EQ:
                // Hint must be different than expected length
            case LE:
            case LT: {
                // Hint must be larger than expected length
                byte[] hint = new byte[expectedLength + 1];
                for (int i = 0 ; i < genSol.length ; i++)
                    hint[i] = (byte) genSol[i]; // Different types, cannot arrayCopy
                hint[hint.length - 1] = 'a';
                hints.add(new Coordinator.StringHint(new String(hint), Coordinator.HintType.Z3));
                // TODO
                return new byte[0];
            }
            default:
                return null;
        }
    }

    private Optional<Coordinator.Input> replaceEqualsByStartsWith(Map<String, Expression> res, Expression cs) {
        // Check if the constraint is EQUALS

        AtomicReference<String> hack = new AtomicReference<>();

        Expression newCS = cs.copy(new Copier() {
            @Override
            public Expression copy(Operation operation) {
                if (operation.getOperator() != Operation.Operator.EQUALS)
                    return super.copy(operation);

                if (operation.getOperand(1) instanceof StringConstant)
                    hack.set(((StringConstant)operation.getOperand(1)).getValue());

                return postCopy(operation, new Operation(Operation.Operator.STARTSWITH, operation.getOperand(0), operation.getOperand(1)));
            }
        });

        // TODO try to find string
        if (hack.get() == null)
            return Optional.empty();

        ArrayList<AbstractMap.SimpleEntry<String, Object>> sat = new ArrayList<>();
        HashSet<String> unsat = new HashSet<>();

        // Our new modified constraint
        res.put("special", newCS);

        Coordinator.StringHint hint = null;

//        if (argumentToEquals instanceof StringConstant) {
//            // We know what's the argument to equals
//           hint = new Coordinator.StringHint(((StringConstant)argumentToEquals).getValue(), Coordinator.HintType.Z3);
//        } else {
//            // TODO we need to ask Z3 to give us what is the argument to equals
//            // TODO the code below was a try but it doesn't quite work, it always gets UNSAT
//            // TODO probably some silly reason
////            // A string variable that is large enough for us to read what we just compared against
////            int n = 50;
////            Expression auxStringVar = new StringVariable("aux");
////            for (int i = 0 ; i < 50 ; i++) {
////                auxStringVar = new Operation(Operation.Operator.CONCAT, auxStringVar, new BVVariable("aux"+i, 32));
////            }
////
////            res.put("aux1", new Operation(Operation.Operator.STARTSWITH, auxStringVar, argumentToEquals));
//            return Optional.empty();
//        }

        solve(res, sat, unsat);


        if (!unsat.isEmpty()) {
            // No good, didn't work
            res.remove("special");
            return Optional.empty();
        } else {
            HashMap<String, byte[]> genFuncs = new HashMap<>();
            Coordinator.Input ret = new Coordinator.Input();
            ret.bytes = solutionToInput(sat, genFuncs);

            Map<String, Expression> resForHints = new HashMap<>();
            resForHints.put("special", newCS);
            ret.hints = generatorsToHints(res.values(), genFuncs);

            for (Coordinator.StringHint[] h : ret.hints) {
                if (h == null)
                    continue;

                for (int i = 0 ; i < h.length ; i++)
                    h[i].hint = hack.get();
            }

            res.remove("special");
            LinkedList<Coordinator.StringHint[]> hs = generatorsToHints(res.values(), genFuncs);
            for (int i = 0 ; i < ret.hints.size() ; i++) {
                if (ret.hints.get(i) == null)
                    ret.hints.set(i, hs.get(i));
            }
            return Optional.of(ret);
//            // It worked, get the string and the solution
//            res.remove("c" + (res.size()-1));
//
//            // Get size of solution
//            int size = 0;
//            for (AbstractMap.SimpleEntry<String, Object> e : sat) {
//                if (e.getKey().startsWith("autoVar_")) {
//                    try {
//                        int n = Integer.parseInt(e.getKey().replace("autoVar_", ""));
//                        size = Math.max(size, n);
//                    } catch (NumberFormatException ex) {
//                        continue;
//                    }
//                }
//            }
//            byte ret[] = new byte[size+1];
//            for (AbstractMap.SimpleEntry<String, Object> e : sat) {
//                if (e.getKey().startsWith("autoVar_")) {
//                    try {
//                        int n = Integer.parseInt(e.getKey().replace("autoVar_", ""));
//                        ret[n] = ((Integer) e.getValue()).byteValue();
//                    } catch (NumberFormatException ex) {
//                        continue;
//                    }
//                }
//            }
//
//            hints.add(hint);
//            return Optional.of(ret);
        }
    }

    private int solved = 0;
    private void solve(Map<String, Expression> constraints, ArrayList<AbstractMap.SimpleEntry<String, Object>> sat, HashSet<String> unsat) {
        solved += 1;

        if (Z3_OUTPUT_DIR != null) {
            try {
                dumpToTXTFile(Paths.get(Z3_OUTPUT_DIR.getAbsolutePath(), "constraints" + solved + ".txt").toFile(), constraints);
            } catch (IOException e) {
                // That's ok, we tried
                e.printStackTrace();
            }
        }

        // Initialize Z3 instance
        Instance in = new Instance(data.green, null, constraints);
        for (Z3JavaTranslator.Z3GreenBridge e : data.optionGenerator.generateOptions(data.modeler.getUnderlyingExpr(in)))
            data.stateStore.addOption(e);

        Z3JavaTranslator.Z3GreenBridge newExp = data.stateStore.getNewOption();
        boolean issat = false;
        final String prefix = "autoVar_";
        while (newExp != null && !issat) {
            issat = true;
//					System.out.println("Trying out new version: " + newExp);
            try{
                @SuppressWarnings("unchecked")
                long start = System.currentTimeMillis();


                ModelZ3JavaService.Solution sol = data.modeler.solve(newExp);

                if (sol.sat) {
//					System.out.println("SAT");
//								System.out.println("SAT: " + sol);
                    for(String v : sol.data.keySet())
                    {
                        sat.add(new AbstractMap.SimpleEntry<>(v, sol.data.get(v)));
                    }
                } else {
//					System.out.println("NOT SAT");
                    for (String k : sol.data.keySet()) {
                        unsat.add(k);
                    }
                    issat = false;
                }
            }
            catch(NotSatException ex)
            {
                issat = false;
                System.out.println("Not sat");
            }
            newExp = data.stateStore.getNewOption();
        }

        Collections.sort(sat, new Comparator<AbstractMap.SimpleEntry<String, Object>>() {
            @Override
            public int compare(AbstractMap.SimpleEntry<String, Object> o1, AbstractMap.SimpleEntry<String, Object> o2) {
                if (o1.getKey().startsWith(prefix) && o2.getKey().startsWith(prefix)) {
                    Integer i1 = Integer.valueOf(o1.getKey().substring(prefix.length()));
                    Integer i2 = Integer.valueOf(o2.getKey().substring(prefix.length()));
                    return i1.compareTo(i2);
                }

                return o1.getKey().compareTo(o2.getKey());
            }
        });
    }

    private void dumpToTXTFile(File file, Map<String, Expression> constraints) throws IOException {
        Map<String, Expression> res = new HashMap<>();

        try (PrintStream ps = new PrintStream(new BufferedOutputStream(new FileOutputStream(file)))) {
            ps.println("(set-option :produce-unsat-cores true)");

            Context ctx = new Context();
            {
                // Get all variables into a new translator
                Z3JavaTranslator translator = new Z3JavaTranslator(ctx);

                for (Expression e : constraints.values())
                    try {
                        e.accept(translator);
                    } catch (VisitorException e1) {
                        throw new Error(e1);
                    }

                // Declare functions
                for (String function : translator.getFunctions().keySet())
                    ps.println("(declare-fun " + function + " (Int (_ BitVec 32)) (_ BitVec 32))");

                // Declare variables
                HashSet<String> seen = new HashSet<>();
                for (Expr v : translator.getVariableMap().values()) {
                    if (seen.add(v.toString())) {
                        Sort s = v.getSort();
                        ps.println("(declare-const " + v + " " + s + ")");
                    }
                }
            }

            // Print constraints
            for (Map.Entry<String, Expression> entry : constraints.entrySet()) {
                Z3JavaTranslator t = new Z3JavaTranslator(ctx);
                try {
                    entry.getValue().accept(t);
                } catch (VisitorException e1) {
                    throw new Error(e1);
                }

                // Print constraint number as a comment
                ps.println("; c" + entry.getKey());

                // Print Knarr constraint as comment
                ps.println("; " + entry.getValue().toString());

                ps.println("(assert (!" + t.getTranslation() + " :named " + entry.getKey() + "))");
                ps.println();
            }

            // Check model
            ps.println("(check-sat)");
            ps.println("(get-model)");

            ps.println("; uncomment below to get unsat core");
            ps.println(";(get-unsat-core)");
        }
    }

    private static class Data {
        Green green;
        ModelFactorizerService slicer;
        ModelCanonizerService canonizer;
        ModelZ3JavaService modeler;
        Map<Variable, Variable> variableMap;
        StateStore stateStore;
        ConstraintOptionGenerator optionGenerator;
    }

    public static class Target {
        Coordinator.Branch branch;
        byte[] input;
        List<Expression> constraints;
        HashMap<Integer, HashSet<Coordinator.StringHint>> hints;

        public Target(Coordinator.Branch branch, byte[] input, List<Expression> constraints, HashMap<Integer, HashSet<Coordinator.StringHint>> hints) {
            this.branch = branch;
            this.constraints = constraints;
            this.hints = hints;
            this.input = input;
        }
    }
}
