package edu.berkeley.cs.jqf.fuzz.central;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import edu.gmu.swe.knarr.server.ConstraintOptionGenerator;
import edu.gmu.swe.knarr.server.HashMapStateStore;
import edu.gmu.swe.knarr.server.StateStore;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.expr.VisitorException;
import za.ac.sun.cs.green.service.canonizer.ModelCanonizerService;
import za.ac.sun.cs.green.service.factorizer.ModelFactorizerService;
import za.ac.sun.cs.green.service.z3.ModelZ3JavaService;
import za.ac.sun.cs.green.service.z3.Z3JavaTranslator;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.NotSatException;

import java.io.*;
import java.nio.file.Paths;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Properties;

public class Z3Worker extends Worker {
    private LinkedList<LinkedList<Expression>> constraints = new LinkedList<>();
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

    public Z3Worker() {
        super(null, null);
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

    @Override
    protected void work() throws IOException, ClassNotFoundException {
        // Set timeout
        {
            String to;
            if ((to = System.getProperty("Z3_TIMEOUT")) != null)
                Z3JavaTranslator.timeoutMS = Integer.parseInt(to);
            else
                Z3JavaTranslator.timeoutMS = 3600 * 1000; // 1h
        }

        int solved = -1;
        while (true) {
            solved++;
            LinkedList<Expression> csToSolve;

            synchronized (constraints) {
                if (constraints.isEmpty()) {
                    try {
                        constraints.wait();
                    } catch (InterruptedException _) {
                    }
                    continue;
                }

                csToSolve = constraints.removeFirst();
            }

            Map<String, Expression> res = new HashMap<>();
            for (Expression e : csToSolve)
                res.put("c" + res.size(), e);
            ArrayList<AbstractMap.SimpleEntry<String, Object>> sat = new ArrayList<>();
            HashSet<String> unsat = new HashSet<>();

            sat.clear();
            unsat.clear();
            solve(res, sat, unsat);

            if (Z3_OUTPUT_DIR != null)
                dumpToTXTFile(Paths.get(Z3_OUTPUT_DIR.getAbsolutePath(), "constraints" + solved + ".txt").toFile(), res);

            for (String s : unsat)
                System.out.println(res.get(s));

            continue;
        }
    }

    private void solve(Map<String, Expression> constraints, ArrayList<AbstractMap.SimpleEntry<String, Object>> sat, HashSet<String> unsat) {

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
               // for (String function : translator.getFunctions().keySet())
                 //   ps.println("(declare-fun " + function + " (Int (_ BitVec 32)) (_ BitVec 32))");

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

    public void addConstraints(LinkedList<Expression> cs) {
        synchronized (this.constraints) {
            this.constraints.addLast(cs);
            this.constraints.notifyAll();
        }
    }

    public void addConstraints(String filename) {
        // Deserialization
        try
        {
            File file = new File(filename);
            // Reading the object from a file
            FileInputStream fis = new FileInputStream(file);
            ObjectInputStream in = new ObjectInputStream(fis);

            LinkedList<Expression> constraints = (LinkedList<Expression>)in.readObject();

            in.close();
            fis.close();

            synchronized (this.constraints) {
                this.constraints.addLast(constraints);
                this.constraints.notifyAll();
            }

        }

        catch(IOException ex)
        {
            System.out.println("Could not de-serialize constraints");
        }

        catch(ClassNotFoundException ex)
        {
            System.out.println("ClassNotFoundException is caught");
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
}
