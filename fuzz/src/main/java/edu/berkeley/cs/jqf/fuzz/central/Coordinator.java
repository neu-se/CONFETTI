package edu.berkeley.cs.jqf.fuzz.central;

import za.ac.sun.cs.green.expr.Expression;

import java.io.*;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.BinaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Coordinator implements Runnable {
    private LinkedList<Input> inputs = new LinkedList<>();
    private ConcurrentHashMap<Branch, Branch> branches = new ConcurrentHashMap<>();
    private HashMap<Input, HashSet<StringHint>> perInputStringEqualsHints = new HashMap<>();
    private ConcurrentHashMap<Input, HashMap<Integer, HashSet<StringHint>>> perByteStringEqualsHints = new ConcurrentHashMap<>();
    private HashSet<StringHint> globalStringEqualsHints = new HashSet<>();

    private HashMap<Integer, Set<Branch>> seenBranches = new HashMap<>();

    private ConcurrentHashMap<Input, ConstraintRepresentation> constraints = new ConcurrentHashMap<>();
    private KnarrWorker knarr;
    private Z3Worker z3;
    private ZestWorker zest;

    protected Boolean z3Started = false;

    private final Config config;

    public Coordinator(Config config) {
        this.config = config;
    }


    protected final synchronized void foundInput(int id, byte[] bytes, boolean valid, LinkedList<StringHint[]>hints, LinkedList<int[]> instructions, Double coveragePercentage, long numExecutions, Integer score, LinkedList<int[]> requestOffsets) {
        Input in = new Input();
        in.bytes = bytes;
        in.id = id;
        in.isNew = (config.useInvalid ? true : valid);
        in.hints = hints;
        in.instructions = instructions;
        in.coveragePercentage = coveragePercentage;
        in.numExecutions = numExecutions;
        in.score = score;
        in.isValid = valid;
        in.requestsForRandom = requestOffsets;

        this.inputs.addLast(in);
        this.notifyAll();
    }

    protected final synchronized Input getInput(int index) {

        for(int i = 0; i < this.inputs.size(); i++) {

            if (this.inputs.get(i).id == index)
                return this.inputs.get(i) ;
        }
        return null;
    }

    private void update_score( LinkedList<Branch> bs, Input input) {
        Integer temp_score = 0;
        Integer starting_branch_score = config.branchPriorityDecayFunctionStartingValue;
        for(int i = 0; i < bs.size(); i++) {
            Set<Branch> seen = null;
            if(seenBranches.containsKey(i)) {
                if(!seenBranches.get(i).contains(bs.get(i))) {
                    seen = seenBranches.get(i);
                    if(!seen.contains(bs.get(i))) {
                        seen.add(bs.get(i));
                        temp_score += starting_branch_score;
                    }
                }
            }
            else {
                HashSet<Branch> hs = new HashSet<>();
                hs.add(bs.get(i));
                seenBranches.put(i, hs);
                temp_score += starting_branch_score;
            }

            starting_branch_score = config.branchPriorityDecayFunctionOperation.operation(starting_branch_score, config.branchPriorityDecayFunctionValue);
        }

        if(temp_score > 0 ) {
            input.score = input.score + temp_score;
            zest.addUpdatedInputScore(input);
        }

    }

    @Override
    public void run() {
        HashMap<Integer, TreeSet<Integer>> lastRecommendation = new HashMap<>();

        while (true) {
            ArrayList<Input> m;

            synchronized (this) {
                boolean newInputs = false;

                if (this.knarr != null) {

                    // if for some reason z3 isn't started, start it here
                    if (config.usez3Hints && !z3Started) {
                        if (this.z3 == null)
                            this.z3 = new Z3Worker(zest, knarr, config.filter);
                        startZ3Thread();
                    }
                    for (Input i : inputs) {
                        if (i.isNew) {
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

                m = new ArrayList<>(inputs);
                //m.sort((o1, o2) -> o1.isValid && !o2.isValid ? -1 : o1.isValid == o2.isValid ? 0 : 1);
                //don't sort, it will starve invalid inputs from being processed.

                //DEBUG/profiling:
                int numNewInputs = 0;
                int numNewValidInputs = 0;
                int numNewInvalidInputs = 0;
                for(Input i : inputs){
                    if(i.isNew){
                        numNewInputs++;
                        if(i.isValid){
                            numNewValidInputs++;
                        }else{
                            numNewInvalidInputs++;
                        }
                    }
                }
                System.out.println("Knarr queue size: " + numNewInputs + " ("+numNewValidInputs+" valid, " + numNewInvalidInputs+" invalid)");

            }

            int n = 0;
            for (Input input : m) {
                if (input.isNew) {
                    if (n++ > 10)
                        break;
                    // Get constraints from Knarr
                    LinkedList<Expression> cs;
                    try {
                        cs = knarr.getConstraints(input);
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
                    long start = System.currentTimeMillis();
                    KnarrWorker.constraintsProcessed = 0;
                    for (Expression e : cs)
                        KnarrWorker.process(bs, eqs, e, config.filter);
                    long end = System.currentTimeMillis();
                    System.out.println("Processed " + KnarrWorker.constraintsProcessed + " constraints in " + (end - start));

                    update_score(bs, input);
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
                    if(input.isNew || input.recommendedBefore){
                        continue;
                    }
                    input.recommendedBefore = true;
                    TreeSet<Integer> recommendation = new TreeSet<>();
                    for (Branch branch : branches.values()) {
                        //We need to recommend things even if they weren't used in a branch that wasn't explored -
                        //otherwise we miss out big on ability to find new paths!!!!
                        //if (branch.falseExplored.isEmpty() || branch.trueExplored.isEmpty() || branch.keep) {
                            if (branch.control.containsKey(input)) {
                                for (int i : branch.control.get(input)){
                                    recommendation.add(i);
                                }
                            }
                        //}
                    }

                    if (!lastRecommendation.containsKey(input.id) || !recommendation.equals(lastRecommendation.get(input.id))) {
                        //System.out.println(input.id + " -> " + recommendation);
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

                    if(recommendation.size() > 0){
                        System.out.println("Recommendation for " + input.id);
                        for(Integer i : recommendation){
                            System.out.println("\t"+i+": " + stringEqualsHints.get(i));
                        }
                    }
                    //input.allHints = stringEqualsHints;
                    //input.recs = new LinkedList<>(recommendation);
                    if(recommendation.size() > 0){
                        zest.recommend(input.id, recommendation, stringEqualsHints);
                    }
                }
            }
        }
    }

    public final synchronized  void setKnarrWorker(KnarrWorker knarr, ZestWorker zest) {
        this.knarr = knarr;
        this.zest = zest;

        if(config.usez3Hints) {
            this.z3 = new Z3Worker(zest, knarr, config.filter);
            startZ3Thread();
        }

    }

    public final synchronized void startZ3Thread() {
        this.z3Started = true;
        new Thread("CONFETTI Z3 Worker") {
            @Override
            public void run() {
                z3Thread();
            }
        }.start();
        this.notifyAll();

    }
    private Boolean isInWhitelist(String branchname) {

        if (config.regexFilter == null)
            return true;
        else {

            // Create a pattern from regex
            Pattern pattern
                    = Pattern.compile(config.regexFilter);


            // Create a matcher for the input String
            Matcher matcher
                    = pattern
                    .matcher(branchname);

            // Get the possible result
            // using lookingAt() method
            return matcher.lookingAt();
        }
       // return branchname.contains("org/mozilla/javascript/CodeGenerator") || branchname.contains("org/mozilla/javascript/optimizer");
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
                            .filter(b -> isInWhitelist(b.source))
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
            Z3Worker.Target target = new Z3Worker.Target(inputToTarget, top, inputToTarget.bytes, constraints.get(inputToTarget).getExpressions(), perByteStringEqualsHints.get(inputToTarget));

            // Send target to Z3
            Optional<Coordinator.Input> newInput = z3.exploreTarget(target);

            // Updated inputs/branches tried
            z3tried.get(top).add(inputToTarget);

            // Handle result
            if (newInput.isPresent()) {
                System.out.println("Z3 found new input for " + inputToTarget.id + " " + target.branch.source);
                zest.addInputFromZ3(newInput.get());
            }
        }
    }

    public Config getConfig() {
        return this.config;
    }

    public static class Input implements Externalizable {
        public int id;
        public byte[] bytes;
        public LinkedList<int[]> instructions;
        public boolean recommendedBefore;
        //We store the set of random requests from the original input - if we use Z3
        // to generate some hints, we'll need to position them using this
        public LinkedList<int[]> requestsForRandom;
        boolean isNew;
        public double coveragePercentage;
        public long numExecutions;
        public LinkedList<StringHint[]> hints;
        public Integer score = 0;
        public boolean isValid;
        public LinkedList<StringHintGroup> hintGroups;

        public Input(){

        }

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

        @Override
        public void writeExternal(ObjectOutput out) throws IOException {
            out.writeInt(id);
            out.writeInt(bytes.length);
            out.write(bytes);
            if(instructions == null){
                out.writeInt(-1);
            }else {
                out.writeInt(instructions.size());
                for (int[] inst : instructions) {
                    out.writeObject(inst);
                }
            }
            out.writeBoolean(recommendedBefore);
            if (requestsForRandom == null) {
                out.writeInt(-1);
            } else {
                out.writeInt(requestsForRandom.size());
                for (int[] req : requestsForRandom) {
                    out.writeObject(req);
                }
            }
            out.writeBoolean(isNew);
            out.writeDouble(coveragePercentage);
            out.writeLong(numExecutions);
            if (hints == null) {
                out.writeInt(-1);
            } else {
                out.writeInt(hints.size());
                for (StringHint[] h : hints) {
                    out.writeObject(h);
                }
            }
            out.writeInt(score);
            out.writeBoolean(isValid);
            if (hintGroups == null) {
                out.writeInt(-1);
            } else {
                out.writeInt(hintGroups.size());
                for (StringHintGroup g : hintGroups) {
                    out.writeObject(g);
                }
            }
        }

        @Override
        public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
            this.id = in.readInt();
            this.bytes = new byte[in.readInt()];
            in.readFully(this.bytes);
            this.instructions = new LinkedList<>();
            int nInsn = in.readInt();
            for(int i = 0; i < nInsn; i++){
                this.instructions.add((int[]) in.readObject());
            }
            this.recommendedBefore = in.readBoolean();
            int nReqs = in.readInt();
            this.requestsForRandom = new LinkedList<>();
            for(int i = 0; i < nReqs; i++){
                this.requestsForRandom.add((int[]) in.readObject());
            }
            this.isNew = in.readBoolean();
            this.coveragePercentage = in.readDouble();
            this.numExecutions = in.readLong();
            int nHints = in.readInt();
            this.hints = new LinkedList<>();
            for(int i = 0; i < nHints; i++){
                this.hints.add((StringHint[]) in.readObject());
            }
            this.score = in.readInt();
            this.isValid = in.readBoolean();
            int nHintGroups =in.readInt();
            this.hintGroups = new LinkedList<>();
            for(int i = 0; i < nHintGroups; i++){
                this.hintGroups.add((StringHintGroup) in.readObject());
            }
        }
    }


    public static class StringHintGroup implements Externalizable{
        public LinkedList<int[]> instructions = new LinkedList<>();
        public LinkedList<StringHint> hints = new LinkedList<>();

        public StringHintGroup(){

        }
        @Override
        public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
            int nInsns = in.readInt();
            for(int i = 0; i < nInsns; i++){
                this.instructions.add((int[]) in.readObject());
            }
            int nHints = in.readInt();
            for(int i = 0; i < nHints; i++){
                this.hints.add((StringHint) in.readObject());
            }
        }

        @Override
        public void writeExternal(ObjectOutput out) throws IOException {
            out.writeInt(instructions.size());
            for(int[] insns : instructions){
                out.writeObject(insns);
            }
            out.writeInt(hints.size());
            for(StringHint h : hints){
                out.writeObject(h);
            }
        }

        @Override
        public String toString() {
            StringBuilder ret = new StringBuilder("StringHintGroup:\n");
            for (int i = 0; i < instructions.size(); i++) {
                ret.append('\t');
                int[] insn = instructions.get(i);
                ret.append(insn[0]);
                ret.append('-');
                ret.append(insn[0] + insn[1]);
                ret.append(':');
                ret.append('"');
                ret.append(hints.get(i));
                ret.append('"');
                ret.append('\n');
            }
            return ret.toString();
        }
    }

    /**
     * A StringHint is a value that we want to try in a position in an input
     * There is a parallel vector that tracks where each hint goes.
     * StringHints are applied independently, unless they are part of a StringHintGroup
     */
    public static class StringHint implements Externalizable {
        private static final long serialVersionUID = -1812382770909515539L;
        String hint;
        HintType type;
        transient HashSet<String> debugSources;

        public StringHint(){

        }
        public StringHint(String hint, HintType type, HashSet<String> debugSources){
            this(hint, type);
            this.debugSources = debugSources;
        }
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
        public String toString() {
            return "StringHint{" +
                    "hint='" + hint + '\'' +
                    ", type=" + type +
                    ", debugSources=" + debugSources +
                    '}';
        }

        @Override
        public int hashCode() {
            return Objects.hash(hint, type);
        }

        @Override
        public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
            this.hint = in.readUTF();
            int hintType = in.readInt();
            if(hintType == -1)
                this.type = null;
            else
                this.type = HintType.values()[hintType];
        }

        @Override
        public void writeExternal(ObjectOutput out) throws IOException {
            out.writeUTF(this.hint);
            if(this.type == null){
                out.writeInt(-1);
            }else{
                out.writeInt(this.type.ordinal());
            }
        }
    }
    public enum HintType {
        EQUALS,
        INDEXOF, //Currently we will also add a startsWith and an endsWith
        STARTSWITH,
        ENDSWITH,
        LENGTH,
        ISEMPTY,
        Z3
    }
    public static class Branch implements Externalizable {
        private static final long serialVersionUID = -6900391468143442577L;
        public int takenID, notTakenID;
        public boolean result, keep;
        public HashSet<Integer> controllingBytes;
        public String source = "";

        transient HashMap<Input, Integer[]> control;
        transient HashSet<Input> trueExplored;
        transient HashSet<Input> falseExplored;

        public Branch(){

        }
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

        @Override
        public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
            this.takenID = in.readInt();
            this.notTakenID = in.readInt();
            this.result = in.readBoolean();
            this.keep = in.readBoolean();
            int nBytes = in.readInt();
            if(nBytes != -1)
                this.controllingBytes = new HashSet<>();
            for(int i = 0; i < nBytes; i++)
                this.controllingBytes.add(in.readInt());
            this.source = in.readUTF();
        }

        @Override
        public void writeExternal(ObjectOutput out) throws IOException {
            out.writeInt(this.takenID);
            out.writeInt(this.notTakenID);
            out.writeBoolean(this.result);
            out.writeBoolean(this.keep);
            if(this.controllingBytes == null)
                out.writeInt(-1);
            else{
                out.writeInt(this.controllingBytes.size());
                for(Integer i : this.controllingBytes)
                    out.writeInt(i);
            }
            out.writeUTF(this.source);
        }
    }

    public static class Config {
        public enum Hinting { NONE, GLOBAL, PER_INPUT, PER_BYTE }

        public interface Arithmetic {
            int operation(int a, int b);
        }

        public  HashMap<String, Config.Arithmetic> operations  = new HashMap<>();

        public final String[] filter;

        public final String regexFilter;
        public final Hinting hinting;

        public final boolean useInvalid;
        public final boolean useConstraints;

        public final boolean usez3Hints;

        public final boolean doNotUseHints;

        public final String constraintsPath;

        public final boolean triggerZ3;

        public final int triggerZ3SampleWindow;

        public final double triggerZ3SampleThreshold;
        public final int branchPriorityDecayFunctionValue;
        public final Arithmetic branchPriorityDecayFunctionOperation;
        public final int branchPriorityDecayFunctionStartingValue;

        public Config(Properties p) {

            operations.put("+", (int a, int b) -> (a + b));
            operations.put("-", (int a, int b) -> (a - b));
            operations.put("/", (int a, int b) -> (a / b));
            operations.put("*", (int a, int b) -> (a * b));

            {
                String f = p.getProperty("path.filter");
                filter = (f == null) ? null : f.split(",");
            }

            {
                regexFilter = p.getProperty("regex.filter");
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

                doNotUseHints = (p.getProperty("doNotUseHints") != null);
                String sampleWindow;
                if((sampleWindow = p.getProperty("triggerZ3SampleWindow")) != null) {
                    triggerZ3SampleWindow = Integer.parseInt(sampleWindow);
                } else triggerZ3SampleWindow = -1;

                String sampleThreshold;
                if((sampleThreshold = p.getProperty("triggerZ3SampleThreshold")) != null) {
                    triggerZ3SampleThreshold = Double.parseDouble(sampleThreshold);
                } else triggerZ3SampleThreshold = Double.MAX_VALUE;


                String branchPriorityDecayFunction = p.getProperty("branchPriorityDecayFunction");
                if(branchPriorityDecayFunction != null) {
                    branchPriorityDecayFunctionStartingValue = Integer.parseInt(branchPriorityDecayFunction.split(",")[2]);
                    branchPriorityDecayFunctionValue = Integer.parseInt(branchPriorityDecayFunction.split(",")[1]);
                    branchPriorityDecayFunctionOperation = operations.get(branchPriorityDecayFunction.split(",")[0]);
                } else {
                    branchPriorityDecayFunctionValue = 0;
                    branchPriorityDecayFunctionStartingValue = 0;
                    branchPriorityDecayFunctionOperation = operations.get("+");
                }
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
