package edu.berkeley.cs.jqf.fuzz.central;

import edu.gmu.swe.knarr.server.ConstraintOptionGenerator;
import edu.gmu.swe.knarr.server.HashMapStateStore;
import edu.gmu.swe.knarr.server.StateStore;
import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.Instance;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Variable;
import za.ac.sun.cs.green.service.canonizer.ModelCanonizerService;
import za.ac.sun.cs.green.service.factorizer.ModelFactorizerService;
import za.ac.sun.cs.green.service.z3.ModelZ3JavaService;
import za.ac.sun.cs.green.service.z3.Z3JavaTranslator;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.NotSatException;

import java.io.IOException;
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
    Data data;

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

        while (true) {
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

    public void addConstraints(LinkedList<Expression> cs) {
        synchronized (this.constraints) {
            this.constraints.addLast(cs);
            this.constraints.notifyAll();
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
