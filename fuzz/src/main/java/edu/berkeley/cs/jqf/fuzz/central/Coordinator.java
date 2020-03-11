package edu.berkeley.cs.jqf.fuzz.central;

import za.ac.sun.cs.green.expr.Expression;

import java.io.*;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.BinaryOperator;

public class Coordinator implements Runnable {
    private LinkedList<Input> inputs = new LinkedList<>();
    private ConcurrentHashMap<Branch, Branch> branches = new ConcurrentHashMap<>();
    private HashMap<Input, HashSet<StringHint>> perInputStringEqualsHints = new HashMap<>();
    private ConcurrentHashMap<Input, HashMap<Integer, HashSet<StringHint>>> perByteStringEqualsHints = new ConcurrentHashMap<>();
    private HashSet<StringHint> globalStringEqualsHints = new HashSet<>();



    private ConcurrentHashMap<Input, ConstraintRepresentation> constraints = new ConcurrentHashMap<>();
    private KnarrWorker knarr;
    private Z3Worker z3;
    private ZestWorker zest;

    private Boolean startZ3;
    private Boolean z3Started = false;


    private Input windowStartInput = null;
    private Double maxCoveragePercentageInWindow = 0.0;


    private final Config config;

    public Coordinator(Config config) {
        this.config = config;
        this.startZ3 = config.triggerZ3 ? false : true;
    }

    protected final synchronized void foundInput(int id, byte[] bytes, boolean valid, LinkedList<StringHint[]>hints, Double coveragePercentage, long numExecutions) {
        Input in = new Input();
        in.bytes = bytes;
        in.id = id;
        in.isNew = (config.useInvalid ? true : valid);
        in.hints = hints;
        in.coveragePercentage = coveragePercentage;
        in.numExecutions = numExecutions;


        this.inputs.addLast(in);

        // sliding window - determine if we start z3 or not

        if (!z3Started && this.windowStartInput == null) {
            this.windowStartInput = in;
            this.maxCoveragePercentageInWindow = in.coveragePercentage;
        }
        else if(this.windowStartInput != null && (in.numExecutions - this.windowStartInput.numExecutions) < this.config.triggerZ3SampleWindow) {
            if(in.coveragePercentage > this.maxCoveragePercentageInWindow) {
                if((in.coveragePercentage - this.maxCoveragePercentageInWindow) > this.config.triggerZ3SampleThreshold)
                    this.windowStartInput = in;
                this.maxCoveragePercentageInWindow = in.coveragePercentage;
            }
        } else if(this.windowStartInput != null && (in.numExecutions - this.windowStartInput.numExecutions) >= this.config.triggerZ3SampleWindow) {
            if((maxCoveragePercentageInWindow - windowStartInput.coveragePercentage) < this.config.triggerZ3SampleThreshold) {
                System.out.println("STARTING Z3 THREAD NOW!!!!!");
                startZ3Thread();
                windowStartInput = null;
                maxCoveragePercentageInWindow = 0.0;
            } else {
                this.windowStartInput = in;
                this.maxCoveragePercentageInWindow = in.coveragePercentage;
            }
        }
//        } else if (this.windowStartInput != null && ((in.id - this.windowStartInput.id) < this.config.triggerZ3SampleWindow)) {
//            this.maxCoveragePercentageInWindow = Double.max(this.maxCoveragePercentageInWindow, in.coveragePercentage);
//        } else if (this.windowStartInput != null && ((in.id - this.windowStartInput.id) == this.config.triggerZ3SampleWindow) ) {
//            if((maxCoveragePercentageInWindow - windowStartInput.coveragePercentage) > this.config.triggerZ3SampleThreshold) {
//                startZ3Thread();
//                windowStartInput = null;
//                maxCoveragePercentageInWindow = 0.0;
//            } else {
//                this.windowStartInput = in;
//                this.maxCoveragePercentageInWindow = in.coveragePercentage;
//            }
//        }

        //this.inputs.addFirst(in);
        this.notifyAll();

        System.out.println("Input added " + id);
        if(!hints.isEmpty())
            System.out.println("HINTS FOUND! " + hints);
    }

    protected final synchronized Input getInput(int index) {
        return this.inputs.get(index);
    }


    @Override
    public void run() {
        HashMap<Integer, TreeSet<Integer>> lastRecommendation = new HashMap<>();

        while (true) {
            LinkedList<Input> m;

            synchronized (this) {
                boolean newInputs = false;

                if (this.knarr != null) {
                    if (!z3Started && startZ3) {
                        startZ3Thread();
                    }
                    for (Input i : inputs) {
                        if (i.isNew) {
//                            if (!z3Started && i.coveragePercentage >= config.triggerZ3SampleThreshold)
//                                startZ3 = true;
                            newInputs = true;
                            break;
                        }
                    }
                }
                if (!newInputs) {
                    try {
                        this.wait();
                        continue;
                    } catch (InterruptedException e) {
                        continue;
                    }
                }

                m = new LinkedList<>(inputs);
            }

            int n = 0;
            for (Input input : m) {
                if (input.isNew) {
                    if (n++ > 10)
                        break;
                    // Get constraints from Knarr
                    LinkedList<Expression> cs;
                    try {
                        cs = knarr.getConstraints(input.bytes, input.hints);
                    } catch (IOException e) {
                        throw new Error(e);
                    }

                    if (config.useConstraints) {
                        // Keep track of constraints, either filenames or in memory
                        if (config.constraintsPath != null) {

                            String filename = config.constraintsPath + "/input_" + input.id;
                            //Saving of object in a file
                            FileOutputStream file = null;
                            try {
                                file = new FileOutputStream(filename);
                                ObjectOutputStream out = null;
                                out = new ObjectOutputStream(file);

                                // Serialize the constraints
                                out.writeObject(cs);

                                out.close();
                                file.close();
                            } catch (FileNotFoundException e) {
                                e.printStackTrace();
                            } catch (IOException e) {
                                e.printStackTrace();
                            }

                            this.constraints.put(input, new ConstraintRepresentation(filename));
                        } else {
                            this.constraints.put(input, new ConstraintRepresentation(cs));
                        }


                    }
                    //z3.addConstraints(input.id, cs);
                    // Compute coverage and branches from constraints
                    LinkedList<Branch> bs = new LinkedList<>();
                    HashMap<Integer, HashSet<StringHint>> eqs = new HashMap<>();
                    for (Expression e : cs)
                        knarr.process(bs, eqs, e);

                    // Adjust string hints
                    if (!eqs.isEmpty()) {
                        switch (config.hinting) {
                            case NONE:
                                break;
                            case GLOBAL:
                                for (HashSet<StringHint> s : eqs.values())
                                    globalStringEqualsHints.addAll(s);
                                break;
                            case PER_INPUT:
                                HashSet<StringHint> ss = new HashSet<>();
                                for (HashSet<StringHint> s : eqs.values())
                                    ss.addAll(s);
                                perInputStringEqualsHints.put(input, ss);
                                break;
                            case PER_BYTE:
                                perByteStringEqualsHints.put(input, eqs);
                                break;
                            default:
                                throw new Error("Not implemented");
                        }

                    }


                    {
                        ListIterator<Branch> iter = bs.listIterator(0);
                        while (iter.hasNext()) {
                            Branch b = iter.next();

                            for (String f : config.filter) {
                                if (b.source != null && b.source.contains(f)) {
                                    iter.remove();
                                    break;
                                }
                            }
                        }
                    }

                    // Check if any previous branches were explored
                    branches: for (Branch b : bs) {
                        if (b.source == null || b.controllingBytes.isEmpty())
                            continue;

                        for (String f : config.filter)
                            if (b.source.contains(f))
                                continue branches;

                        Branch existing;
                        if (!branches.containsKey(b)) {
                            existing = b;
                            existing.trueExplored = new HashSet<>();
                            existing.falseExplored = new HashSet<>();
                            existing.control = new HashMap<>();
                            existing.keep = b.keep;
                            existing.source = (b.source == null ? "" : b.source);
                            branches.put(b, b);
                        } else {
                            existing = branches.get(b);
                        }

                        synchronized (existing) {
                            if (b.result) {
                                if (existing.trueExplored.isEmpty())
                                    System.out.println("\tInput " + input.id + " explores T on " + existing.takenID + " (" + existing.source + ")");
                                existing.trueExplored.add(input);
                            } else {
                                if (existing.falseExplored.isEmpty())
                                    System.out.println("\tInput " + input.id + " explores F on " + existing.takenID + " (" + existing.source + ")");
                                existing.falseExplored.add(input);
                            }
                        }

                        LinkedList<Integer> bytes = new LinkedList<>(b.controllingBytes);
                        Collections.sort(bytes);

                        existing.control.put(input, bytes.toArray(new Integer[0]));
                    }

                    input.isNew = false;
                }
            }

            // Make recommendations
            synchronized (this) {
                for (Input input : inputs) {
                    TreeSet<Integer> recommendation = new TreeSet<>();
                    for (Branch branch : branches.values()) {
                        if (branch.falseExplored.isEmpty() || branch.trueExplored.isEmpty() || branch.keep) {
                            if (branch.control.containsKey(input)) {
                                for (int i : branch.control.get(input))
                                    recommendation.add(i);
                            }
                        }
                    }

                    if (!lastRecommendation.containsKey(input.id) || !recommendation.equals(lastRecommendation.get(input.id))) {
                        System.out.println(input.id + " -> " + recommendation);
                        lastRecommendation.put(input.id, recommendation);
                    }

                    HashMap<Integer, HashSet<StringHint>> stringEqualsHints = new HashMap<>();
                    switch (config.hinting) {
                        case NONE:
                            break;
                        case GLOBAL:
                            recommendation.clear();
                            HashSet<StringHint> globals = new HashSet<>(globalStringEqualsHints);
                            for (int i = 0 ; i < input.bytes.length ; i++) {
                                stringEqualsHints.put(i, globals);
                            }
                            break;
                        case PER_INPUT:
                            recommendation.clear();
                            HashSet<StringHint> perInput = new HashSet<>(perInputStringEqualsHints.getOrDefault(input, new HashSet<>()));
                            for (int i = 0 ; i < input.bytes.length ; i++) {
                                stringEqualsHints.put(i, perInput);
                            }
                            break;
                        case PER_BYTE:
                            stringEqualsHints.putAll(perByteStringEqualsHints.getOrDefault(input, new HashMap<>()));
                            break;
                        default:
                            throw new Error("Not implemented");
                    }

                    zest.recommend(input.id, recommendation, stringEqualsHints);
                }
            }
        }
    }

    public final synchronized  void setKnarrWorker(KnarrWorker knarr, ZestWorker zest) {
        this.knarr = knarr;
        this.zest = zest;
        this.z3 = new Z3Worker(zest, knarr, config.filter);

        if(config.usez3Hints && startZ3)
            startZ3Thread();

    }

    public final synchronized void startZ3Thread() {
        this.z3Started = true;
        new Thread() {
            @Override
            public void run() {
                z3Thread();
            }
        }.start();
        this.notifyAll();

    }

    private void z3Thread() {
        HashMap<Branch, Set<Input>> z3tried = new HashMap<>();

        out: while (true) {
            // Figure out what is the branch that needs the most attention
            HashSet<Branch> triedTops = new HashSet<>();
            Branch top = null;
            Input inputToTarget = null;
            while (triedTops.size() < branches.size()) {
                Set<Input> triedInputs;

                {
                    Optional<Branch> maybeTop = branches.values().stream()
                            .filter(b -> b.source != null)
                            .filter(b -> !triedTops.contains(b))
                            .filter(b -> b.falseExplored.isEmpty() || b.trueExplored.isEmpty())
                            .reduce(BinaryOperator.maxBy(Comparator.comparingInt(o -> o.trueExplored.size() + o.falseExplored.size())));

                    if (!maybeTop.isPresent())
                        continue out;
                    else
                        top = maybeTop.get();
                }

                triedInputs = z3tried.getOrDefault(top, new HashSet<>());
                if (triedInputs.isEmpty())
                    z3tried.put(top, triedInputs);

                // Create Z3 target
                {
                    Branch stupidLambdasInJavaDontCaptureTheEnvironment = top;
                    Optional<Input> maybeInputToTarget;
                    synchronized (this) {
                        maybeInputToTarget = inputs.stream()
                                .filter(i -> triedInputs != null && !triedInputs.contains(i))
                                .filter(i -> stupidLambdasInJavaDontCaptureTheEnvironment.trueExplored.contains(i) || stupidLambdasInJavaDontCaptureTheEnvironment.falseExplored.contains(i))
                                .reduce(BinaryOperator.maxBy(Comparator.comparingInt(o -> o.bytes.length)));
                    }

                    if (!maybeInputToTarget.isPresent()) {
                        triedTops.add(top);
                        continue;
                    } else {
                        inputToTarget = maybeInputToTarget.get();
                        break;
                    }
                }
            }

            // We have no input, try again until we do
            if (inputToTarget == null)
                continue;


            // Set Z3 target
            Z3Worker.Target target = new Z3Worker.Target(top, inputToTarget.bytes, constraints.get(inputToTarget).getExpressions(), perByteStringEqualsHints.get(inputToTarget));

            // Send target to Z3
            Optional<Coordinator.Input> newInput = z3.exploreTarget(target);

            // Updated inputs/branches tried
            z3tried.get(top).add(inputToTarget);

            // Handle result
            if (newInput.isPresent()) {
                System.out.println("Z3 found new input for " + inputToTarget.id);
//                try {
//                    // Send input to knarr, check if we explore target
//                    LinkedList<Expression> updatedConstraints = knarr.getConstraints(newInput.get().bytes, newInput.get().hints);
//                    Optional<Expression> hit = updatedConstraints.stream().filter(e -> e.metadata instanceof Coverage.BranchData && ((Coverage.BranchData)e.metadata).source.equals(target.branch.source)).findFirst();
//
//                    if (hit.isPresent()) {
//                        // This input hits the target, add it to JQF
                        zest.addInputFromZ3(newInput.get());
//                    }

                    for(StringHint[] hint : newInput.get().hints) {
                        System.out.println(hint);
                    }
//                } catch (IOException e) {
//
//                }
            }
        }
    }

    public Config getConfig() {
        return this.config;
    }

    public static class Input implements Serializable {
        int id;
        public byte[] bytes;
        boolean isNew;
        public double coveragePercentage;
        public long numExecutions;
        public LinkedList<StringHint[]> hints;

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Input input = (Input) o;
            return id == input.id;
        }

        @Override
        public int hashCode() {
            return Objects.hash(id);
        }
    }


    public static class StringHint implements Serializable {
        String hint;
        HintType type;

        public StringHint(String hint, HintType type) {
            this.hint = hint;
            this.type = type;
        }

        public HintType getType() {
            return this.type;
        }

        public String getHint() {
            return this.hint;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            StringHint that = (StringHint) o;
            return hint.equals(that.hint) &&
                    type == that.type;
        }

        @Override
        public int hashCode() {
            return Objects.hash(hint, type);
        }
    }
    public enum HintType {
        EQUALS,
        Z3
    }
    public static class Branch implements Serializable {
        public int takenID, notTakenID;
        public boolean result, keep;
        public HashSet<Integer> controllingBytes;
        public String source = "";

        transient HashMap<Input, Integer[]> control;
        transient HashSet<Input> trueExplored;
        transient HashSet<Input> falseExplored;

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Branch branch = (Branch) o;
            return takenID == branch.takenID &&
                    notTakenID == branch.notTakenID;
        }

        @Override
        public int hashCode() {
            return Objects.hash(takenID, notTakenID);
        }
    }

    public static class Config {
        public enum Hinting { NONE, GLOBAL, PER_INPUT, PER_BYTE }

        public final String[] filter;
        public final Hinting hinting;

        public final boolean useInvalid;
        public final boolean useConstraints;

        public final boolean usez3Hints;

        public final String constraintsPath;

        public final boolean triggerZ3;

        public final int triggerZ3SampleWindow;

        public final double triggerZ3SampleThreshold;

        public Config(Properties p) {
            {
                String f = p.getProperty("path.filter");
                filter = (f == null) ? null : f.split(",");
            }
            {
                Hinting h;
                try {
                    h = Hinting.valueOf(p.getProperty("string.hints"));
                } catch (IllegalArgumentException _) {
                    h = Hinting.NONE;
                }

                hinting = h;
            }
                useInvalid = (p.getProperty("useInvalid") != null);
            {
                constraintsPath = p.getProperty("constraintsPath");
                useConstraints = (p.getProperty("useConstraints") != null);
                usez3Hints = (p.getProperty("usez3Hints") != null);

                triggerZ3 = (p.getProperty("triggerZ3") != null);

                String sampleWindow;
                if((sampleWindow = p.getProperty("triggerZ3SampleWindow")) != null) {
                    triggerZ3SampleWindow = Integer.parseInt(sampleWindow);
                } else triggerZ3SampleWindow = -1;

                String sampleThreshold;
                if((sampleThreshold = p.getProperty("triggerZ3SampleThreshold")) != null) {
                    triggerZ3SampleThreshold = Double.parseDouble(sampleThreshold);
                } else triggerZ3SampleThreshold = Double.MAX_VALUE;

            }
        }
    }

    public static class ConstraintRepresentation {
        private  LinkedList<Expression> expr;
        private  String exprFile;

        ConstraintRepresentation(LinkedList<Expression> e) {
            this.expr = e;
            this.exprFile = null;
        }
        ConstraintRepresentation(String exprFile) {
            this.expr = null;
            this.exprFile = exprFile;
        }


        private LinkedList<Expression> readConstraintsFromFile() {

            FileInputStream fileIn = null;
            try {
                fileIn = new FileInputStream(this.exprFile);
                ObjectInputStream objectIn = new ObjectInputStream(fileIn);
                Object constraints = objectIn.readObject();
                fileIn.close();
                return (LinkedList<Expression>) constraints;

            } catch (FileNotFoundException e) {
                return null;
            } catch (IOException e) {
                return null;
            } catch (ClassNotFoundException e) {
                return null;
            }
        }

        public LinkedList<Expression> getExpressions() {

            return this.expr != null ? this.expr : readConstraintsFromFile();
        }

    }
}
