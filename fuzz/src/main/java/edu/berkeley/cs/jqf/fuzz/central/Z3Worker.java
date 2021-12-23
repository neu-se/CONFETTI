package edu.berkeley.cs.jqf.fuzz.central;

import com.microsoft.z3.*;
import edu.gmu.swe.knarr.runtime.Coverage;
import edu.gmu.swe.knarr.server.ConstraintOptionGenerator;
import edu.gmu.swe.knarr.server.HashMapStateStore;
import edu.gmu.swe.knarr.server.StateStore;
import org.eclipse.collections.api.iterator.IntIterator;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.expr.*;
import za.ac.sun.cs.green.service.canonizer.ModelCanonizerService;
import za.ac.sun.cs.green.service.factorizer.ModelFactorizerService;
import za.ac.sun.cs.green.service.z3.ModelZ3JavaService;
import za.ac.sun.cs.green.service.z3.Z3JavaTranslator;
import za.ac.sun.cs.green.util.Configuration;

import java.io.*;
import java.math.BigInteger;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Z3Worker {
    private Data data;

    private static final File Z3_OUTPUT_DIR;

    static final boolean PRINT_Z3_DEBUG_INFO = false;

    static PrintWriter statsLogger;

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
        String z3StatsFile = System.getProperty("z3StatsLog");
        if(z3StatsFile != null){
            try {
                statsLogger = new PrintWriter(new BufferedWriter(new FileWriter(z3StatsFile)));
                Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
                    @Override
                    public void run() {
                        if(statsLogger != null)
                            statsLogger.close();
                    }
                }));
                statsLogger.println("time,numBranchesUnsolved,selectedBranch,numInputsNotTried,selectedInput,timeSpent,result");
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
    static long campaignStart = System.currentTimeMillis();

    public static void appendToLogFile(int numBranchesUnsolved, String selectedBranch, int numInputsNotTried, int numInputsTried, int selectedInput, int timeSpent, String result){

        if(statsLogger != null) {
            statsLogger.println(String.format("%d,%d,%s,%d,%d,%d,%d,%s",
                    (System.currentTimeMillis() - campaignStart),
                    numBranchesUnsolved,
                    selectedBranch,
                    numInputsNotTried,
                    numInputsTried, selectedInput, timeSpent, result
            ));
            statsLogger.flush();
        }
    }

    private static final int EXTRA_ZEROES_FOR_Z3 = Integer.parseInt(System.getProperty("extraZeroesForZ3", "0"));

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

    private static byte[] solutionToInput(ArrayList<AbstractMap.SimpleEntry<String, Object>> sat, Map<String, byte[]> funcs) {
        // Get size of solution
        int size = 0;
        HashMap<String, Integer> solvedStringLengths = new HashMap<>();
        for (AbstractMap.SimpleEntry<String, Object> e : sat) {
            if (e.getKey().startsWith("autoVar_")) {
                try {
                    int n = Integer.parseInt(e.getKey().replace("autoVar_", ""));
                    size = Math.max(size, n);
                } catch (NumberFormatException ex) {
                    continue;
                }
            } else if (e.getKey().startsWith("solved_gen")) {
                String str = e.getKey().substring("solved_".length());
                String genName = str.substring(0, str.indexOf('_'));
                int idx = Integer.valueOf(str.substring(str.indexOf('_') + 1));
                if (!solvedStringLengths.containsKey(genName)) {
                    solvedStringLengths.put(genName, idx);
                }
                if (idx > solvedStringLengths.get(genName)) {
                    solvedStringLengths.put(genName, idx);
                }
            }
        }


        for(String genFunc : solvedStringLengths.keySet()){
            int strLen = solvedStringLengths.get(genFunc);
            byte[] bs = new byte[strLen + 1];
            funcs.put(genFunc, bs);
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
            } else if(e.getKey().startsWith("solved_gen")){
                String str = e.getKey().substring("solved_".length());
                String genName = str.substring(0, str.indexOf('_'));
                int idx = Integer.valueOf(str.substring(str.indexOf('_') + 1));
                funcs.get(genName)[idx] = ((Integer) e.getValue()).byteValue();
            }
        }


        // Handle solutions to generator functions
        //sat.stream().filter(entry -> entry.getKey().startsWith("gen"))
        //        .forEach(entry -> funcs.put(entry.getKey(), intArrToByteArr((int[])entry.getValue())));

        return ret;
    }

    private static byte[] intArrToByteArr(int[] arr) {
        byte[] ret = new byte[arr.length];
        // This is slow, surely there's a better way...
        for (int i = 0 ; i < ret.length ; i++)
            ret[i] = (byte) arr[i];

        return ret;
    }
    private static LinkedList<Expression> createCaptureVariables(Iterable<Expression> constraints){
        HashSet<String> capturedVariables = new HashSet<>();
        LinkedList<Expression> ret = new LinkedList<>();
        for(Expression e : constraints){
            try {
                e.accept(new Visitor() {
                    @Override
                    public void postVisit(FunctionCall function) throws VisitorException {
                        super.postVisit(function);
                        if(function.getName().startsWith("gen")){
                            int idx = (int) ((IntConstant)function.getArguments()[0]).getValueLong();
                            String varName = "solved_"+function.getName()+"_"+idx;
                            if(capturedVariables.add(varName)){
                                ret.add(new BinaryOperation(Operation.Operator.EQ, new BVVariable(varName, 32), new FunctionCall(function.getName(), function.getArguments())));
                            }
                        }
                    }
                });
            } catch (VisitorException visitorException) {
                visitorException.printStackTrace();
            }
        }
        return ret;
    }

    static class CharEqualityFindingVisitor extends Visitor{
        private HashSet<FunctionCall> generatorCalls = new HashSet<>();
        @Override
        public void postVisit(FunctionCall function) throws VisitorException {
            if(function.getName().startsWith("gen")){
                generatorCalls.add(function);
            }
            super.postVisit(function);
        }

        public HashSet<FunctionCall> getGeneratorCalls() {
            return generatorCalls;
        }
    }
    private Optional<Coordinator.Input> negateConstraint(Target t, Set<Expression> hints) throws TimeoutException {

        Map<String, Expression> res = new HashMap<>();

        Expression targetConstraint = null;

//        for (Expression e : hints)
//            res.put("c" + res.size(), e);
        if(PRINT_Z3_DEBUG_INFO)
            System.out.println("Trying to use Z3 to get to " + t.branch + (t.arm != -1 ? " arm#" + t.arm : "") + " using input #" + t.originalInput.id);

        for (Expression e : t.constraints) {
            if (e.metadata instanceof Coverage.BranchData) {
                Coverage.BranchData data = (Coverage.BranchData) e.metadata;
                if (data.takenCode == t.branch.takenID) {
                    targetConstraint = e;
                    break;
                }
            } else if (e.metadata instanceof Coverage.SwitchData) {
                Coverage.SwitchData data = (Coverage.SwitchData) e.metadata;
                if (data.switchID == t.branch.takenID) {
                    if (data.arm == t.arm) {
                        targetConstraint = e;
                        break;
                    } else {
                        continue; //Don't add constraints for other arms.
                    }
                }
            }
            res.put("c" + res.size(), e);
        }
        //Add string function captures
        for(Expression e : createCaptureVariables(t.constraints)){
            res.put("stringSolve"+res.size(), e);
        }

        if (targetConstraint == null)
            throw new IllegalStateException();
        if(PRINT_Z3_DEBUG_INFO) {
            System.out.println("To negate:");
            System.out.println(targetConstraint);
        }

        // If we are negating something like char == 'A', we might end up solving it to char == '\0', which has a special
        // meaning, and will likely not end up making any sense.
        try {
            CharEqualityFindingVisitor v = new CharEqualityFindingVisitor();
            targetConstraint.accept(v);
            for (FunctionCall strChar : v.getGeneratorCalls()) {
                //res.put("c" + res.size(), new BinaryOperation(Operation.Operator.NE, strChar, new IntConstant(0)));
                res.put("c" + res.size(), new BinaryOperation(Operation.Operator.AND, new BinaryOperation(Operation.Operator.GT, new IntConstant(128), strChar),
                        new BinaryOperation(Operation.Operator.GT, strChar, new IntConstant(0))));

            }
        } catch (VisitorException e) {
            e.printStackTrace();
        }

        // Negate the target constraint
        Expression negatedTargetConstraint = new UnaryOperation(Operation.Operator.NOT, targetConstraint);

        // Try to solve it
        res.put("c" + res.size(), negatedTargetConstraint);
        ArrayList<AbstractMap.SimpleEntry<String, Object>> sat = new ArrayList<>();
        HashSet<String> unsat = new HashSet<>();
        solve(res, sat, unsat);

        if (unsat.isEmpty()) {
            if(PRINT_Z3_DEBUG_INFO)
                System.out.println("Z3 found solution for " + t.branch);
            // Solution found, generate input
            HashMap<String, byte[]> genFuncs = new HashMap<>();
            Coordinator.Input ret = new Coordinator.Input();
            ret.bytes = solutionToInput(sat, genFuncs);
            Coordinator.StringHintGroup hg = generatorsToHints(res.values(), genFuncs, t.originalInput);
            if(hg != null){
                if(ret.hintGroups == null){
                    ret.hintGroups = new LinkedList<>();
                }
                ret.hintGroups.add(hg);
                if(PRINT_Z3_DEBUG_INFO)
                    System.out.println(hg);
            }

            // Add more bytes to maybe explore new paths
            if (EXTRA_ZEROES_FOR_Z3 > 0) {
                byte[] bytes = new byte[ret.bytes.length + EXTRA_ZEROES_FOR_Z3];
                System.arraycopy(ret.bytes, 0, bytes, 0, ret.bytes.length);
                ret.bytes = bytes;
            }

            return Optional.of(ret);
        } else {
            if(PRINT_Z3_DEBUG_INFO) {
                System.out.println("Z3 failed to solve for " + t.branch + unsat);
                for (String each : unsat) {
                    System.out.println("\t" + res.get(each));
                }
            }
            if (unsat.size() == 1) {
                // Try to fix single UNSAT expression

                // Remove UNSAT expression
                Expression ex = res.remove(unsat.stream().findFirst().get());

                // Maybe it's a String.equals without enough size?
                StringEqualsFindingVisitor equalsFindingVisitor = new StringEqualsFindingVisitor();
                try{
                    ex.accept(equalsFindingVisitor);
                } catch (VisitorException e) {
                    e.printStackTrace();
                    return Optional.empty();
                }
                LinkedList<BinaryOperation> strEqualsExprs = equalsFindingVisitor.getStrEqualsExprs();
                if(!strEqualsExprs.isEmpty()) {
                    if(PRINT_Z3_DEBUG_INFO)
                        System.out.println("Transforming unsat str equals exprs: " + ex);
                    // Make a copy of this expression, replacing each of the String.equals operations with versions that
                    // force the symbolic part to be of the right length
                    Copier copier = new Copier() {
                        @Override
                        public Expression copy(BinaryOperation operation) {
                            if (strEqualsExprs.contains(operation)) {
                                Expression ret = replaceStringsInEqualsWithCorrectLength(res, operation, t);
                                if (ret != null) {
                                    return ret;
                                }
                            }
                            return super.copy(operation);
                        }
                    };
                    Expression withCorrectLength = copier.copy(ex);
                    if(PRINT_Z3_DEBUG_INFO)
                        System.out.println(withCorrectLength);
                    if (withCorrectLength != null) {
                        res.put(unsat.stream().findFirst().get(), withCorrectLength);
                        sat.clear();
                        unsat.clear();
                        solve(res, sat, unsat);
                        if (unsat.isEmpty()) {
                            if(PRINT_Z3_DEBUG_INFO)
                                System.out.println("Z3 found solution after failing w string hack for " + t.branch);
                            // Solution found, generate input
                            HashMap<String, byte[]> genFuncs = new HashMap<>();
                            Coordinator.Input ret = new Coordinator.Input();
                            ret.bytes = solutionToInput(sat, genFuncs);
                            Coordinator.StringHintGroup hg = generatorsToHints(res.values(), genFuncs, t.originalInput);
                            if (hg != null) {
                                if (ret.hintGroups == null) {
                                    ret.hintGroups = new LinkedList<>();
                                }
                                ret.hintGroups.add(hg);
                            }

                            // Add more bytes to maybe explore new paths
                            if (EXTRA_ZEROES_FOR_Z3 > 0) {
                                byte[] bytes = new byte[ret.bytes.length + EXTRA_ZEROES_FOR_Z3];
                                System.arraycopy(ret.bytes, 0, bytes, 0, ret.bytes.length);
                                ret.bytes = bytes;
                            }

                            return Optional.of(ret);
                        }else{
                            if(PRINT_Z3_DEBUG_INFO) {
                                System.out.println("Z3 failed even after string hacking: " + unsat);
                                for (String each : unsat)
                                    System.out.println("\t" + res.get(each));
                            }
                        }
                    }
                }
            }
            if (!hints.isEmpty())
                return negateConstraint(t, new HashSet<>());
            return Optional.empty();
        }
    }

    public static Coordinator.StringHintGroup generatorsToHints(Collection<Expression> exps, Map<String, byte[]> genFuncs, Coordinator.Input originalInput) {
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
                                                byte[] bs = entry.getValue();
                                                int length = bs.length;
                                                for(int i = bs.length - 1; i > 0; i--)
                                                {
                                                    if(bs[i] == 0 && i < length){
                                                        length = i;
                                                    }
                                                }
                                                hs.add(new String(bs, 0, length));
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

        Coordinator.StringHintGroup hintGroup = new Coordinator.StringHintGroup();

        int[] lastReqGroup = null;
        for(int i = 0; i < originalInput.requestsForRandom.length; i+=2){
            int offset = originalInput.requestsForRandom[i];
            int length = originalInput.requestsForRandom[i+1];
            if(hints.get(offset) != null){
                Set<String> strings = hints.remove(offset);
                if(PRINT_Z3_DEBUG_INFO && strings.size() > 1){
                    System.err.println("Found multiple strings from Z3 : " + strings);
                    System.err.println("Jon didn't think this was possible, we should figure out what's happening");
                }
                String hint = strings.iterator().next();
                hintGroup.instructions.add(new int[]{offset, length});
                hintGroup.hints.add(new Coordinator.StringHint(hint, Coordinator.HintType.Z3, null));
            }
        }
        if(PRINT_Z3_DEBUG_INFO)
            System.out.println(hintGroup);

        return hintGroup;
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
                            funcHint = new BinaryOperation(
                                    Operation.Operator.AND,
                                    funcHint,
                                    new BinaryOperation(
                                            Operation.Operator.EQ,
                                            new FunctionCall(
                                                    entry.getValue().getName(),
                                                    args
                                            ),
                                            new IntConstant(h.hint.charAt(j))
                                    )
                            );
                        }
                        hintsConstraint = new BinaryOperation(Operation.Operator.OR, hintsConstraint, funcHint);
                    }
                }
            }

            if (foundHints)
                ret.add(hintsConstraint);
        }

        return ret;
    }

    public Optional<Coordinator.Input> exploreTarget(Target t) throws TimeoutException {
        // Set timeout
        {
            String to;
            if ((to = System.getProperty("Z3_TIMEOUT")) != null)
                Z3JavaTranslator.timeoutMS = Integer.parseInt(to);
            else
//                Z3JavaTranslator.timeoutMS = 3600 * 1000; // 1h
                Z3JavaTranslator.timeoutMS = 10 * 1000; // 10s
        }

        try {

//            if (!isTargetFeasible(t)) {
//                // TODO tell the coordinator that this target is not feasible
//                return Optional.empty();
//            }

            Set<Expression> stringHintConstraints = hintsToConstraints(t.constraints, t.hints);
            Optional<Coordinator.Input> input = negateConstraint(t, stringHintConstraints);

            return input;

        } catch(TimeoutException ex){
            throw ex;
        } catch (Z3Exception | ClassCastException e) {
            System.err.println(e.getMessage());
            e.printStackTrace();
        } catch (Throwable e) {
            System.err.println(e.getMessage());
            e.printStackTrace();
        }

        return Optional.empty();
    }
    static class AutoVarVisitor extends Visitor {
        private IntArrayList autoVars = new IntArrayList(4);
        @Override
        public void postVisit(BVVariable variable) throws VisitorException {
            if(variable.getName().startsWith("autoVar_")){
                int idx = Integer.parseInt(variable.getName().substring("autoVar_".length()));
                autoVars.add(idx);
            }
        }
        public boolean hasAutoVars(){
            return autoVars.size() > 0;
        }
        public int getFirstAutoVar(){
            IntIterator iter = autoVars.intIterator();
            int min = Integer.MAX_VALUE;
            while(iter.hasNext()){
                int x = iter.next();
                if(x < min)
                    min = x;
            }
            return min;
        }
        public int getNumAutoVars(){
            return autoVars.size();
        }
    }

    static class GeneratedCharacter {
        public String functionName;
        public int index;
        public Expression source;
        public int bytePositionInRandomGen;
        public int numBytesInRandomGen;

        public GeneratedCharacter(String functionName, int index, Expression source) {
            this.functionName = functionName;
            this.index = index;
            this.source = source;
            AutoVarVisitor autoVarVisitor = new AutoVarVisitor();
            try{
                source.accept(autoVarVisitor);
                if(autoVarVisitor.hasAutoVars()){
                    this.bytePositionInRandomGen = autoVarVisitor.getFirstAutoVar();
                    this.numBytesInRandomGen = autoVarVisitor.getNumAutoVars();
                }
            } catch (VisitorException e) {
                e.printStackTrace();
            }
        }

        public static GeneratedCharacter fromFunction(FunctionCall fn) {
            if(fn.getName().startsWith("gen")){
                return new GeneratedCharacter(fn.getName(), (int) ((IntConstant)fn.getArguments()[0]).getValueLong(), fn.getArguments()[1]);
            }
            return null;
        }

        @Override
        public String toString() {
            return "SymbChar{" +
                    "gen='" + functionName + '\'' +
                    ", index=" + index +
                    '}';
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            GeneratedCharacter that = (GeneratedCharacter) o;
            return index == that.index &&
                    Objects.equals(functionName, that.functionName);
        }

        @Override
        public int hashCode() {
            return Objects.hash(functionName, index);
        }
    }

    static class GeneratedCharacterFinder extends Visitor {
        private GeneratedCharacter character;
        private boolean invalid;

        public void reset(){
            character = null;
            invalid = false;
        }

        public GeneratedCharacter getCharacter() {
            if(invalid)
                return null;
            return character;
        }

        @Override
        public void postVisit(Operation operation) throws VisitorException {
            super.postVisit(operation);
            //for(int i = 0; i < operation.getArity(); i++){
            //    operation.getOperand(i).accept(this);
            //}
        }

        @Override
        public void preVisit(Expression expression) throws VisitorException {
            super.preVisit(expression);
            if(expression instanceof FunctionCall){
                FunctionCall fn = (FunctionCall) expression;
                if(fn.getName().startsWith("gen")){
                    if(this.character != null){
                        this.invalid = true;
                    }
                    this.character = GeneratedCharacter.fromFunction(fn);
                }
            }
        }
    }
    static class StringEqualsFindingVisitor extends Visitor {
        LinkedList<BinaryOperation> strEqualsExprs = new LinkedList<>();
        @Override
        public void preVisit(Operation operation) throws VisitorException {
            super.preVisit(operation);
            switch (operation.getOperator()) {
                case EQUALS:
                case EQUALSIGNORECASE:
                case STARTSWITH:
                case ENDSWITH:
                    this.strEqualsExprs.add((BinaryOperation) operation);
                    break;
            }
        }

        public LinkedList<BinaryOperation> getStrEqualsExprs() {
            return strEqualsExprs;
        }
    }
    static class StringEqualsVisitor extends Visitor {
        private StringVariable stringVariable;
        private LinkedList<Integer> concreteChars = new LinkedList<>();
        private LinkedList<GeneratedCharacter> symbolicChars = new LinkedList<>();
        private StringConstant stringConstant;
        private String generatorFunctionName;
        private HashSet<String> generatorFunctionNames = new HashSet<>();
        private Expression expression;
        private boolean containsConcatOrStringEquals;
        private boolean hasConcretePrefix;

        public StringEqualsVisitor(Expression expression) {
            this.expression = expression;
        }

        public Expression getExpression() {
            return expression;
        }

        public HashSet<String> getGeneratorFunctionNames() {
            return generatorFunctionNames;
        }

        public int getLength(){
            if(this.stringConstant != null){
                return this.stringConstant.getValue().length();
            }
            return concreteChars.size() + symbolicChars.size();
        }

        public boolean isSimpleGeneratorFunctionExpression() {
            return !containsConcatOrStringEquals && symbolicChars.size() == 1 && this.stringVariable == null;
        }

        public boolean hasSymbolicVariable(){
            return !this.symbolicChars.isEmpty();
        }

        public boolean hasStringConstant(){
            return this.stringConstant != null;
        }

        public LinkedList<Integer> getConcreteChars() {
            return concreteChars;
        }

        public boolean hasConcretePrefix() {
            return hasConcretePrefix;
        }

        public StringConstant getStringConstant() {
            return stringConstant;
        }

        public StringVariable getStringVariable() {
            return stringVariable;
        }

        public int getNumConcreteCharsInSymbolic() {
            return concreteChars.size();
        }

        public LinkedList<GeneratedCharacter> getSymbolicChars() {
            return symbolicChars;
        }

        @Override
        public void preVisit(Expression expression) throws VisitorException {
            super.preVisit(expression);
            if(expression instanceof FunctionCall){
                FunctionCall fn = (FunctionCall) expression;
                if(fn.getName().startsWith("gen")){
                    this.generatorFunctionName = fn.getName();
                    this.generatorFunctionNames.add(fn.getName());
                    this.symbolicChars.add(GeneratedCharacter.fromFunction(fn));
                }
            }
        }

        @Override
        public void preVisit(Operation operation) throws VisitorException {
            super.preVisit(operation);
            if(operation.getOperator() == Operation.Operator.EQUALS)
                this.containsConcatOrStringEquals = true;
            if(operation.getOperator() == Operation.Operator.CONCAT){
                this.containsConcatOrStringEquals = true;
                if(operation.getOperand(0) instanceof IntConstant) {
                    if(this.generatorFunctionName == null){
                        this.hasConcretePrefix = true;
                    }
                    concreteChars.add((int) ((IntConstant) operation.getOperand(0)).getValueLong());
                }
                if(operation.getOperand(1) instanceof IntConstant)
                    concreteChars.add((int) ((IntConstant) operation.getOperand(1)).getValueLong());
            }
        }

        @Override
        public void preVisit(StringVariable stringVariable) throws VisitorException {
            super.preVisit(stringVariable);
            if(this.stringVariable != null)
                throw new VisitorException("Found more than one string variable! " + this.stringVariable + " and " + stringVariable);
            this.stringVariable = stringVariable;
        }

        @Override
        public void preVisit(StringConstant stringConstant) throws VisitorException {
            super.preVisit(stringConstant);
            // If we concatenate a string constant into a string, it won't show up as a StringConstant,
            // but instead will be concat of intconstants (each char)
            this.stringConstant = stringConstant;
        }

        public String getFunctionName() {
            return this.generatorFunctionName;
        }
    }

    private static Expression replaceStringsInEqualsWithCorrectLength(Map<String, Expression> res, BinaryOperation strEqualsExpr, Target target) {
        // NEW plan 7-13-21: Modify the string compared so that the ninput.str.equals("abc") && umber of characters matches exactly
        // Add or delete characters from the end of the string
        // If both sides are symbolic, then modify the left hand side to become the length of the right hand side

        boolean isEquals = strEqualsExpr.getOperator() == Operation.Operator.EQUALS || strEqualsExpr.getOperator() == Operation.Operator.EQUALSIGNORECASE;

        Expression leftExpr = strEqualsExpr.getOperand(0);
        Expression rightExpr = strEqualsExpr.getOperand(1);
        StringEqualsVisitor leftStrEquals = new StringEqualsVisitor(leftExpr);
        StringEqualsVisitor rightStrEquals = new StringEqualsVisitor(rightExpr);
        boolean adjustLeft = true;
        try {
            leftExpr.accept(leftStrEquals);
            rightExpr.accept(rightStrEquals);
        } catch (VisitorException e) {
            e.printStackTrace();
        }
        StringEqualsVisitor exprToAdjust;
        StringEqualsVisitor exprToSatisfy;
        //TODO handle all of the cases of left + right
        if(!leftStrEquals.hasSymbolicVariable() && !rightStrEquals.hasSymbolicVariable())
            return null; //shouldn't even be possible, right?
        else if(leftStrEquals.hasSymbolicVariable() && rightStrEquals.hasSymbolicVariable()){
            //Heuristic: If both are symbolic, let's try to satisfy the *longer* one, so we aren't removing chars.
            if(leftStrEquals.getLength() > rightStrEquals.getLength()){
                adjustLeft = false;
                exprToAdjust = rightStrEquals;
                exprToSatisfy = leftStrEquals;
            }else{
                exprToAdjust = leftStrEquals;
                exprToSatisfy = rightStrEquals;
            }
        } else if(leftStrEquals.hasSymbolicVariable()){
            exprToAdjust = leftStrEquals;
            exprToSatisfy = rightStrEquals;
        } else {
            adjustLeft = false;
            exprToAdjust = rightStrEquals;
            exprToSatisfy = leftStrEquals;
        }

        final GeneratedCharacter lastCharInExprToAdjust = exprToAdjust.getSymbolicChars().getLast();
        final int delta = exprToSatisfy.getLength() - exprToAdjust.getLength();
        final HashSet<GeneratedCharacter> callsToRemove = new HashSet<>();
        final GeneratedCharacterFinder finder = new GeneratedCharacterFinder();
        HashSet<String> constraintsToRemove = new HashSet<>();
        if (delta < 0 && isEquals) {
            //Determine which chars to drop
            //Don't every try to drop chars for startsWith or endsWith
            Iterator<GeneratedCharacter> iter = exprToAdjust.getSymbolicChars().descendingIterator();
            while (callsToRemove.size() < 0 - delta && iter.hasNext()){
                GeneratedCharacter each = iter.next();
                if(each.index == 0)
                    continue; //if we have multiple strings, try to always have at least one char in each
                callsToRemove.add(each);
            }

            //Find + remove other constraints on those chars
            for (Map.Entry<String, Expression> each : res.entrySet()) {
                finder.reset();
                try {
                    each.getValue().accept(finder);
                    GeneratedCharacter character = finder.getCharacter();
                    if(callsToRemove.contains(character)){
                        constraintsToRemove.add(each.getKey());
                    }
                } catch (VisitorException e) {
                    e.printStackTrace();
                }
            }
            for(String danglingConstraint : constraintsToRemove){
                res.remove(danglingConstraint);
            }
        }
        Copier transformer = new Copier() {
            @Override
            public Expression copy(BinaryOperation operation) {
                if (operation.getOperator() != Operation.Operator.CONCAT)
                    return super.copy(operation);

                if(delta != 0) {
                    //With the recursive calls, we can only add more chars
                    for (int i = 0; i < 2; i++) {
                        try {
                            finder.reset();
                            operation.getOperand(i).accept(finder);
                            GeneratedCharacter character = finder.getCharacter();
                            if (delta > 0 && character != null && lastCharInExprToAdjust.equals(character)) {
                                //Add delta new characters after this one
                                int addedCount = 0;
                                int otherIndex = i == 0 ? 1 : 0;

                                Expression ret;
                                if (i == 0) {
                                    //We want to add the new chars after the LEFT side of this concat, replacing the right
                                    //with a new concat that ultimately ends with the current right side of this concat
                                    Expression leftExprToadd = operation.getOperand(0);
                                    while (addedCount < delta) {
                                        addedCount++;
                                        leftExprToadd = new BinaryOperation(Operation.Operator.CONCAT, leftExprToadd,
                                                new FunctionCall(lastCharInExprToAdjust.functionName,
                                                        new Expression[]{
                                                                new IntConstant(lastCharInExprToAdjust.index + addedCount),
                                                                character.source}
                                                ));
                                        leftExprToadd.metadata = operation.metadata;
                                    }
                                    //TODO this isn't right if the right side has more concat's, right?
                                    ret = new BinaryOperation(Operation.Operator.CONCAT, leftExprToadd,
                                            operation.getOperand(1));
                                    ret.metadata = operation.metadata;

                                }else{
                                    //We want to add the new chars after the RIGHT side of this concat
                                    ret = new BinaryOperation(Operation.Operator.CONCAT,
                                            operation.getOperand(0), operation.getOperand(1));
                                    ret.metadata = operation.metadata;
                                    while (addedCount < delta) {
                                        addedCount++;
                                        ret = new BinaryOperation(Operation.Operator.CONCAT,
                                                ret, new FunctionCall(lastCharInExprToAdjust.functionName, new Expression[]{new IntConstant(lastCharInExprToAdjust.index + addedCount), character.source}));
                                        ret.metadata = operation.metadata;
                                    }
                                }
                                return postCopy(operation, ret);
                            } else if (character != null && callsToRemove.contains(character)) {
                                //Remove this character
                                int otherIndex = i == 0 ? 1 : 0;
                                Expression ret =  this.copy(operation.getOperand(otherIndex));
                                return ret;
                            }
                        } catch (VisitorException e) {
                            e.printStackTrace();
                        }
                    }
                }
                return super.copy(operation);
            }
        };
        Expression adjustedExpr = transformer.copy(exprToAdjust.getExpression());
        if(adjustLeft)
            return new BinaryOperation(strEqualsExpr.getOperator(), adjustedExpr, exprToSatisfy.getExpression());
        else
            return new BinaryOperation(strEqualsExpr.getOperator(), exprToSatisfy.getExpression(), adjustedExpr);
    }

    static final File Z3_TRANSLATOR_FAILED_DIR = (System.getenv("FAILED_TRANSLATOR_DUMP") == null ? null : new File(System.getenv("FAILED_TRANSLATOR_DUMP")));
    static int numFailedTranslations = 0;
    static ExecutorService translatorService = Executors.newFixedThreadPool(1);
    private static Map<String, BoolExpr> translate(Map<String, Expression> constraints, HashSet<Expr> variables, HashSet<FuncDecl> functions, Context ctx) throws VisitorException, TimeoutException {
        Callable<Map<String, BoolExpr>> task = new Callable<Map<String, BoolExpr>>() {
            @Override
            public Map<String, BoolExpr> call() throws Exception {
                String lastExpr = null;
                try {
                    Z3JavaTranslator translator = new Z3JavaTranslator(ctx);
                    Map<String, BoolExpr> ret = new HashMap<>();

                    for (Map.Entry<String, Expression> e : constraints.entrySet()) {
                            lastExpr = e.getKey();
                            e.getValue().accept(translator);
                            ret.put(e.getKey(), (BoolExpr) translator.getTranslation());
                    }

                    variables.addAll(translator.getVariableMap().values());
                    functions.addAll(translator.getFunctions().values());


                    return ret;
                }catch(Throwable t){
                    numFailedTranslations++;

                    t.printStackTrace();
                    if(Z3_TRANSLATOR_FAILED_DIR != null){
                        if(!Z3_TRANSLATOR_FAILED_DIR.exists())
                            Z3_TRANSLATOR_FAILED_DIR.mkdirs();
                        File outputFile = new File(Z3_TRANSLATOR_FAILED_DIR, numFailedTranslations+"_"+lastExpr+".ser");
                        FileOutputStream fos = new FileOutputStream(outputFile);
                        ObjectOutputStream oos = new ObjectOutputStream(fos);
                        oos.writeObject(constraints);
                        fos.close();
                    }
                    throw t;
                }
            }
        };
        Future<Map<String, BoolExpr>> res = translatorService.submit(task);
        try {
            Map<String, BoolExpr> ret = res.get(Z3JavaTranslator.timeoutMS, TimeUnit.MILLISECONDS);
            return ret;
        } catch (InterruptedException | TimeoutException e) {
            e.printStackTrace();
            throw new TimeoutException(e.getMessage());
        } catch (ExecutionException e) {
            e.printStackTrace();
            throw new TimeoutException(e.getMessage());
        }
    }

    private static int solved = 0;
    private static void solve(Map<String, Expression> constraints, ArrayList<AbstractMap.SimpleEntry<String, Object>> sat, HashSet<String> unsat) throws TimeoutException {
        solved += 1;

        if (Z3_OUTPUT_DIR != null) {
            try {
                dumpToTXTFile(Paths.get(Z3_OUTPUT_DIR.getAbsolutePath(), "constraints" + solved + ".txt").toFile(), constraints);
            } catch (IOException e) {
                // That's ok, we tried
                e.printStackTrace();
            }
        }

        // Create a fresh Z3 Context
        try (Context ctx = new Context()) {

            // Translate from Green to Z3
            HashSet<Expr> vars = new HashSet<>();
            HashSet<FuncDecl> functions = new HashSet<>();
            Map<String, BoolExpr> constraintsInZ3 = translate(constraints, vars, functions, ctx);

            // Get a fresh solver
            Solver solver = ctx.mkSolver();

            // Set the timeout
            {
                Params p = ctx.mkParams();
                p.add("timeout", Z3JavaTranslator.timeoutMS);
                solver.setParameters(p);
            }

            long start = System.currentTimeMillis();
            // Add all the constraints to the current context
            for (Map.Entry<String, BoolExpr> e : constraintsInZ3.entrySet())
                solver.assertAndTrack(e.getValue(), ctx.mkBoolConst(e.getKey()));

            // Solve the constraints
            Status result = solver.check();
            long solvingTime = System.currentTimeMillis() - start;

            if (Status.SATISFIABLE == result) {
                // SAT
//				System.out.println("SAT: " + data.constraints);
                Model model = solver.getModel();
                for (FuncDecl decl : functions) {
                    boolean present = false;
                    for (FuncDecl dd : model.getFuncDecls())
                        if (dd.equals(decl)) {
                            present = true;
                            break;
                        }

                    if (!present)
                        break;

                    FuncInterp z3Val = model.getFuncInterp(decl);
                    // TODO Look at the arguments past first
                    // TODO Support more than BV arguments and BV results
                    // TODO Support more than sequential first arguments
                    int[] funcRes = new int[z3Val.getNumEntries()];
                    for (FuncInterp.Entry e : z3Val.getEntries()) {
                        if (!e.getArgs()[0].isIntNum() || !e.getValue().isBV())
                            throw new Error("Non BV arguments not supported");
                        Long arg = ((IntNum) e.getArgs()[0]).getInt64();
                        Long res = ((BitVecNum) e.getValue()).getLong();
                        if (arg.intValue() >= 0 && arg.intValue() < funcRes.length)
                            funcRes[arg.intValue()] = res.intValue();
                    }

                    sat.add(new AbstractMap.SimpleEntry<>(decl.getName().toString(), funcRes));
                }
                for (Expr z3Var : vars) {
                    Expr z3Val = model.evaluate(z3Var, true);
                    Object val = null;
                    if (z3Val.isIntNum()) {
                        val = Long.parseLong(z3Val.toString());
                    } else if (z3Val.isBV()) {
                        BitVecNum bv = (BitVecNum) z3Val;
                        if (bv.getSortSize() == 64) {
                            // Long
                            BigInteger bi = bv.getBigInteger();
                            val = bi.longValue();
                        } else {
                            // Int
                            Long l = bv.getLong();
                            val = l.intValue();
                        }
                    } else if (z3Val.isRatNum()) {
                        RatNum rt = (RatNum) z3Val;
                        val = ((double) rt.getNumerator().getInt64()) / ((double) rt.getDenominator().getInt64());
                    } else {
                        //Must be string?
                        String sval = z3Val.toString();
                        //Need to clean up string
                        java.util.regex.Pattern p = Pattern.compile("\\\\x(\\d\\d)");
                        Matcher m = p.matcher(sval);
                        while (m.find()) {
                            int i = Long.decode("0x" + m.group(1)).intValue();
                            sval = sval.replace(m.group(0), String.valueOf((char) i));
                        }
                        val = sval;
                    }
                    sat.add(new AbstractMap.SimpleEntry<>(z3Var.toString(), val));
//					String logMessage = "" + greenVar + " has value " + val;
//					log.log(Level.INFO,logMessage);
                }
            } else {
                // UNSAT or Timeout
                BoolExpr[] unsatCore = solver.getUnsatCore();
                for (BoolExpr e : unsatCore) {
                    String key = e.toString();

                    if (key.startsWith("|") && key.endsWith("|"))
                        key = key.substring(1, key.length() - 1);

                    unsat.add(key);
                }
                if (solvingTime >= Z3JavaTranslator.timeoutMS) {
                    throw new TimeoutException("Operation took " + solvingTime + ", timeout=" + Z3JavaTranslator.timeoutMS);
                }
            }
        } catch (VisitorException e) {
            e.printStackTrace();
        }
    }

    private static void dumpToTXTFile(File file, Map<String, Expression> constraints) throws IOException {
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

    public static class Target implements Serializable{
        Coordinator.Branch branch;
        Coordinator.Input originalInput;
        byte[] input;
        List<Expression> constraints;
        HashMap<Integer, HashSet<Coordinator.StringHint>> hints;
        int arm;

        public Target(Coordinator.Input originalInput, Coordinator.Branch branch, int arm, byte[] input, List<Expression> constraints, HashMap<Integer, HashSet<Coordinator.StringHint>> hints) {
            this.originalInput = originalInput;
            this.branch = branch;
            this.constraints = constraints;
            this.hints = hints;
            this.input = input;
            this.arm = arm;
        }
        public Target(Coordinator.Input originalInput, Coordinator.Branch branch, byte[] input, List<Expression> constraints, HashMap<Integer, HashSet<Coordinator.StringHint>> hints) {
            this.originalInput = originalInput;
            this.branch = branch;
            this.constraints = constraints;
            this.hints = hints;
            this.input = input;
            this.arm = -1;
        }
    }
}
