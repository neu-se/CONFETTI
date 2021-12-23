package edu.berkeley.cs.jqf.fuzz.central;

import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance;
import edu.gmu.swe.knarr.ConstraintDeserializer;
import edu.gmu.swe.knarr.runtime.Coverage;
import org.eclipse.collections.api.iterator.IntIterator;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.primitive.IntObjectHashMap;
import org.eclipse.collections.impl.map.mutable.primitive.ObjectIntHashMap;
import org.eclipse.collections.impl.set.mutable.primitive.IntHashSet;
import za.ac.sun.cs.green.expr.Expression;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.TimeoutException;
import java.util.function.BinaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.GZIPInputStream;

public class Coordinator implements Runnable {

    private static final int BRANCH_SOLVES_TIMEOUT = 50; //Give up trying to solve negated constraints for a branch after this many UNSAT returns.
    private static final int MAXIMUM_STRING_EXTENDED_LENGTH = 20; // When building up strings char-by-char, stop adding chars once we reach this point

    private IntObjectHashMap<Input> inputs = new IntObjectHashMap<Input>();
    private ConcurrentHashMap<Branch, Branch> branches = new ConcurrentHashMap<>();
    private HashMap<Input, HashSet<StringHint>> perInputStringEqualsHints = new HashMap<>();
    private IntObjectHashMap<HashMap<Integer, HashSet<StringHint>>> perByteStringEqualsHints = new IntObjectHashMap<>();
    private HashSet<StringHint> globalStringEqualsHints = new HashSet<>();

    private HashMap<Integer, Set<Branch>> seenBranches = new HashMap<>();

    private ConcurrentHashMap<Input, ConstraintRepresentation> constraints = new ConcurrentHashMap<>();
    private KnarrWorker knarr;
    private Z3Worker z3;
    ZestWorker zest;

    protected Boolean z3Started = false;

    private final Config config;

    public Coordinator(Config config) {
        this.config = config;
    }


    protected LinkedList<Input> inputsToSendToKnarr = new LinkedList<>(); //Only used if knarr is not initialized

    protected final void foundInput(int id, byte[] bytes, boolean valid, LinkedList<StringHint[]> hints, LinkedList<int[]> instructions, LinkedList<TargetedHint> targetedHints, Double coveragePercentage, long numExecutions, Integer score, LinkedList<int[]> requestOffsets) {
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
        in.requestsForRandom = new int[requestOffsets.size() * 2];
        int i = 0;
        for (int[] ar : requestOffsets) {
            in.requestsForRandom[i] = ar[0];
            i++;
            in.requestsForRandom[i] = ar[1];
            i++;
        }
        in.targetedHints = new HashSet<>(targetedHints);

        if(this.knarr != null){
            try {
                knarr.sendInputToKnarr(in);
            } catch (IOException e) {
                e.printStackTrace();
            }
        } else{
            this.inputsToSendToKnarr.add(in);
        }

        synchronized (this.inputs){
            this.inputs.put(in.id, in);
        }
    }

    protected final Input getInput(int index) {

        synchronized (this.inputs){
            return this.inputs.get(index);
        }
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

    public void updateBranchCoverageInformation(Branch b, Input input){
        if (b.source == null)
            return;

        Branch existing;
        if (!branches.containsKey(b)) {
            synchronized (branches) {
                existing = branches.get(b);
                if(existing == null) {
                    for (String f : config.filter)
                        if (b.source.contains(f))
                            b.isInFilter = true;
                    existing = b;
                    existing.inputsTried = new IntHashSet();
                    if(b.isSwitch()){
                        //it's a switch branch
                        existing.armsExplored = new IntHashSet[b.armsExplored.length];
                        existing.armsNotExplored = new IntHashSet[b.armsExplored.length];
                        existing.armsSolved = new boolean[b.armsExplored.length];
                        existing.inputsTriedPerArm = new IntHashSet[b.armsExplored.length];
                        for(int i = 0; i < b.armsExplored.length; i++){
                            existing.armsExplored[i] = new IntHashSet();
                            existing.armsNotExplored[i] = new IntHashSet();
                            existing.inputsTriedPerArm[i] = new IntHashSet();
                        }
                    }else {
                        existing.trueExplored = new IntHashSet();
                        existing.falseExplored = new IntHashSet();
                    }
                    existing.control = new IntObjectHashMap<>();
                    existing.keep = b.keep;
                    existing.source = (b.source == null ? "" : b.source);
                    branches.put(b, b);
                }
            }
        } else {
            existing = branches.get(b);
        }

        synchronized (existing) {
            if (b.isSwitch()) {
                for (int i = 0; i < b.armsExplored.length; i++) {
                    if (b.armsExplored[i] != null) {
                        if(b.result) {
                            existing.armsExplored[i].add(input.id);
                            if(!existing.armsNotExplored[i].isEmpty())
                                existing.armsSolved[i] = true;
                        }
                        else {
                            existing.armsNotExplored[i].add(input.id);
                            if(!existing.armsExplored[i].isEmpty())
                                existing.armsSolved[i] = true;
                        }
                        if (existing.armsSolved[i]) {
                            //Check to see if it's fully solved.
                            boolean solved = true;
                            for (int j = 0; j < existing.armsSolved.length; j++) {
                                if (!existing.armsSolved[j]) {
                                    solved = false;
                                    break;
                                }
                            }
                            existing.isSolved = solved;
                        }
                        break;
                    }
                }
            } else {
                if (b.result) {
                    //if (existing.trueExplored.isEmpty())
                    //    System.out.println("\tInput " + input.id + " explores T on " + existing.takenID + " (" + existing.source + ")");
                    existing.trueExplored.add(input.id);
                    if (!existing.falseExplored.isEmpty())
                        existing.isSolved = true;
                } else {
                    //if (existing.falseExplored.isEmpty())
                    //    System.out.println("\tInput " + input.id + " explores F on " + existing.takenID + " (" + existing.source + ")");
                    existing.falseExplored.add(input.id);
                    if (!existing.trueExplored.isEmpty())
                        existing.isSolved = true;
                }
            }
        }
    }

    public void process(LinkedList<Coordinator.Branch> bs, HashMap<Integer, HashSet<Coordinator.StringHint>> stringEqualsArgs, Expression e, Coordinator.Input input) {
        Coverage.CoverageData b = (Coverage.CoverageData) e.metadata;


        if (b == null)
            return;

        Coordinator.Branch bb = new Coordinator.Branch(b);
        bb.controllingBytes = new HashSet<>();

        HashSet<Coordinator.StringHint> eq = new HashSet<>();

        updateBranchCoverageInformation(bb, input);
        Branch existing = branches.get(bb);
        KnarrWorker.findControllingBytes(e, bb.controllingBytes, eq, input, existing == null ? bb : existing); //TODO this can block, it's really bad when it does...
        bs.add(bb);

        IntArrayList bytes = new IntArrayList();
        for(Integer i : bb.controllingBytes)
            bytes.add(i);
        bytes.sortThis();
        if(existing != null)
            existing.control.put(input.id, bytes.toArray());

        if (!eq.isEmpty()) {
            for (Integer i : bb.controllingBytes) {
                HashSet<Coordinator.StringHint> cur = stringEqualsArgs.get(i);
                if (cur == null) {
                    cur = new HashSet<>();
                    stringEqualsArgs.put(i, cur);
                }
                cur.addAll(eq);
            }
        }
    }

    @Override
    public void run() {
        HashMap<Integer, TreeSet<Integer>> lastRecommendation = new HashMap<>();

        synchronized (this.inputs) {
            while (this.knarr == null) {
                try {
                    this.inputs.wait();
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
            }
        }
        while (true) {
            if (this.knarr != null) {
                //TODO can this be safely deleted now?
                // if for some reason z3 isn't started, start it here
                if (config.usez3Hints && !z3Started) {
                    if (this.z3 == null)
                        this.z3 = new Z3Worker(zest, knarr, config.filter);
                    startZ3Thread();
                }
            }

            int n = 0;
            // Get constraints from Knarr
            LinkedList<Expression> cs;
            HashMap<String, String> generatedStrings;
            KnarrWorker.KnarrResponse response = knarr.getConstraintsFromKnarr();
            Input input = null;
            synchronized (inputs) {
                input = inputs.get(response.inputID);
            }

            cs = response.constraints;
            generatedStrings = response.generatedStrings;
            input.generatedStrings = generatedStrings;

            if (config.useConstraints) {
                // Keep track of constraints, either filenames or in memory
                if (config.constraintsPath != null) {
                    this.constraints.put(input, new ConstraintRepresentation(response.fileName));
                } else {
                    this.constraints.put(input, new ConstraintRepresentation(cs));
                }


            }
            //z3.addConstraints(input.id, cs);
            // Compute coverage and branches from constraints
            LinkedList<Branch> bs = new LinkedList<>();
            HashMap<Integer, HashSet<StringHint>> eqs = new HashMap<>();

            input.targetedHints = new HashSet<>();
            long start = System.currentTimeMillis();
            KnarrWorker.constraintsProcessed = 0;
            for (Expression e : cs)
                process(bs, eqs, e, input);
            long end = System.currentTimeMillis();

            //update_score(bs, input);
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
                        synchronized (perByteStringEqualsHints) {
                            perByteStringEqualsHints.put(input.id, eqs);
                        }
                        break;
                    default:
                        throw new Error("Not implemented");
                }

            }

            // Check if any previous branches were explored

            input.isNew = false;

            // Make recommendations
            HashSet<Branch> branchesInThisRecSet = new HashSet<>();
            input.recommendedBefore = true;
            TreeSet<Integer> recommendation = new TreeSet<>();
            for (Branch branch : branches.values()) {
                //We need to recommend things even if they weren't used in a branch that wasn't explored -
                //otherwise we miss out big on ability to find new paths!!!!
                //if (branch.falseExplored.isEmpty() || branch.trueExplored.isEmpty() || branch.keep) {
                if (branch.control.containsKey(input.id)) {
                    branchesInThisRecSet.add(branch);
                    for (int i : branch.control.get(input.id)) {
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
                    for (int i = 0; i < input.bytes.length; i++) {
                        stringEqualsHints.put(i, globals);
                    }
                    break;
                case PER_INPUT:
                    recommendation.clear();
                    HashSet<StringHint> perInput = new HashSet<>(perInputStringEqualsHints.getOrDefault(input, new HashSet<>()));
                    for (int i = 0; i < input.bytes.length; i++) {
                        stringEqualsHints.put(i, perInput);
                    }
                    break;
                case PER_BYTE:
                    synchronized (perByteStringEqualsHints) {
                        HashMap<Integer, HashSet<StringHint>> hints = perByteStringEqualsHints.get(input.id);
                        if (hints == null)
                            hints = new HashMap<>();
                        stringEqualsHints.putAll(hints);
                    }
                    break;
                default:
                    throw new Error("Not implemented");
            }

            //DEBUGGING STRATEGY: print out hints for each rec
            //if(recommendation.size() > 0){
            //    System.out.println("Recommendation for " + input.id);
            //    for(Integer i : recommendation){
            //        System.out.println("\t"+i+": " + stringEqualsHints.get(i));
            //    }
            //}
            //input.allHints = stringEqualsHints;
            //input.recs = new LinkedList<>(recommendation);
            if (recommendation.size() > 0) {
                zest.recommend(input.id, recommendation, stringEqualsHints);
            }
            //for(Branch b : branchesInThisRecSet){
            //    if(b.suggestedHints.size() > 0)
            //        System.out.println(b + " hints:");
            //    for(String h : b.suggestedHints.keySet()){
            //        System.out.println("\t"+b.suggestedHints.get(h)+": " + h);
            //    }
            //}
        }
    }

    public final void setKnarrWorker(KnarrWorker knarr, ZestWorker zest) {
        synchronized (this.inputs) {
            this.knarr = knarr;
            this.knarr.setConfig(config);
            this.zest = zest;

            if (config.usez3Hints) {
                this.z3 = new Z3Worker(zest, knarr, config.filter);
                startZ3Thread();
            }
            this.inputs.notifyAll();
            while(!this.inputsToSendToKnarr.isEmpty()){
                try {
                    this.knarr.sendInputToKnarr(this.inputsToSendToKnarr.pop());
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
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

        //July 18: Jon changed the workloop to be branch first: we'll explore all of the branches once, then start over, picking other inputs
        //Previously, we kept pounding on a single branch, even if it was not possible to satisfy :'(
        boolean hadWork = true;
        out: while (true) {
            try {
                if (!hadWork) {
                    try {
                        Thread.sleep(2000);
                    } catch (InterruptedException e) {
                        e.printStackTrace();
                    }
                }
                hadWork = false;
                // Figure out what is the branch that needs the most attention
                HashSet<Branch> triedTops = new HashSet<>();
                Branch top = null;
                Input inputToTarget = null;
                long num = branches.values().stream()
                        .filter(b -> b.source != null && !b.isInFilter)
                        .filter(b -> !triedTops.contains(b))
                        .filter(b -> isInWhitelist(b.source))
                        .filter(b -> !b.isSolved && !b.isTimedOut)
                        .count();

                //System.out.println("NEW Z3Loop: number of potential branches:" + num);
                while (triedTops.size() < branches.size()) {
                    //Garbage collect constraints that are not going to be useful
                    garbageCollect();

                    //Pick a branch to target
                    Optional<Branch> maybeTop = branches.values().stream()
                            .filter(b -> b.source != null)
                            .filter(b -> !triedTops.contains(b))
                            .filter(b -> isInWhitelist(b.source))
                            .filter(b -> !b.isSolved && !b.isTimedOut)
                            .reduce(BinaryOperator.minBy(Comparator.comparingInt(o -> o.inputsTried.size())));

                    if (!maybeTop.isPresent()) {
                        Z3Worker.appendToLogFile((int) num, "",0,0,0,0,"NO_BRANCHES");
                        continue out; //Start over, allowing for repeated selection of branches
                    } else
                        top = maybeTop.get();

                    // Create Z3 target
                    Branch branchToTarget = top;
                    Optional<Input> maybeInputToTarget;
                    synchronized (this.inputs) {
                        maybeInputToTarget = this.inputs.values().stream()
                                .filter(i -> branchToTarget.isUsefulInputForNegation(i))
                                .reduce(BinaryOperator.minBy(Comparator.comparingInt(o -> o.bytes.length)));
                    }

                    triedTops.add(top);
                    if (!maybeInputToTarget.isPresent()) {
                        //System.out.println("Z3 couldn't find an input to target for " + branchToTarget);
                        Z3Worker.appendToLogFile((int) num, top.source,0,top.inputsTried.size(),0,0,"NO_INPUTS");
                        continue;
                    }

                    long start = System.currentTimeMillis();
                    //System.out.println("Targeting: " + branchToTarget);
                    inputToTarget = maybeInputToTarget.get();
                    top.inputsTried.add(inputToTarget.id);


                    hadWork = true;

                    try {
                        if (top.isSwitch()) {
                            //Try to target each of the arms that haven't been yet fully covered
                            for (int i = 0; i < top.armsSolved.length; i++) {
                                if (!top.armsSolved[i]) {
                                    Z3Worker.Target target = new Z3Worker.Target(inputToTarget, top, i, inputToTarget.bytes, constraints.get(inputToTarget).getExpressions(), perByteStringEqualsHints.get(inputToTarget.id));
                                    Optional<Coordinator.Input> newInput = z3.exploreTarget(target);

                                    Z3Worker.appendToLogFile((int) num, top.source + "_arm" + i, top.getInputsStillUseful().size(), top.inputsTried.size(), inputToTarget.id, (int) (System.currentTimeMillis() - start), newInput.isPresent() ? "SAT" : "UNSAT");

                                    // Handle result
                                    if (newInput.isPresent()) {
                                        //System.out.println("Z3 found new input for " + inputToTarget.id + " " + target.branch.source);
                                        zest.addInputFromZ3(newInput.get(), inputToTarget);
                                    }
                                }
                            }
                        } else {
                            Z3Worker.Target target = new Z3Worker.Target(inputToTarget, top, inputToTarget.bytes, constraints.get(inputToTarget).getExpressions(), perByteStringEqualsHints.get(inputToTarget.id));
                            Optional<Coordinator.Input> newInput = z3.exploreTarget(target);
                            Z3Worker.appendToLogFile((int) num, top.source,top.getInputsStillUseful().size(),top.inputsTried.size(),inputToTarget.id, (int) (System.currentTimeMillis() - start),newInput.isPresent() ? "SAT" : "UNSAT");

                            // Handle result
                            if (newInput.isPresent()) {
                                //System.out.println("Z3 found new input for " + inputToTarget.id + " " + target.branch.source);
                                zest.addInputFromZ3(newInput.get(), inputToTarget);
                            }
                        }

                    } catch (TimeoutException ex) {
                        Z3Worker.appendToLogFile((int) num, top.source,top.getInputsStillUseful().size(),top.inputsTried.size(),inputToTarget.id, (int) (System.currentTimeMillis() - start), "TIMEOUT");

                        ex.printStackTrace();
                        if (top != null && top.trueExplored != null)
                            top.trueExplored.remove(inputToTarget.id);
                        if (top != null && top.falseExplored != null)
                            top.falseExplored.remove(inputToTarget.id);
                        ConstraintRepresentation cr = constraints.get(inputToTarget);
                        long bytes = 0;
                        if (cr != null)
                            bytes = cr.destroy();
                        inputToTarget.evicted = true;
                        for (Branch b : this.branches.values()) {
                            b.evict(inputToTarget.id);
                        }
                        System.err.println("Evicted " + bytes + " of constraints for input #" + inputToTarget.id);
                    }
                    if (top.inputsTried.size() > BRANCH_SOLVES_TIMEOUT) {
                        top.isTimedOut = true;
                    }
                }
            }catch(Throwable t){
                t.printStackTrace();
                //Continue: never allow an exception to end the Z3 thread!
            }
        }
    }

    private long lastGC = 0;
    private void garbageCollect(){
        long start = System.currentTimeMillis();
        if(start - lastGC > 10000 && zest != null) {
            lastGC = start;
            synchronized (this) {
                IntHashSet inputsToKeep = new IntHashSet();
                LinkedList<Branch> branchesToPrune = new LinkedList<>();
                for (Branch b : branches.values()) {
                    if (b.source != null && isInWhitelist(b.source) && !b.isSolved && !b.isTimedOut) {
                        inputsToKeep.addAll(b.getInputsStillUseful());
                    } else {
                        branchesToPrune.add(b);
                    }
                }
                IntArrayList inputsToDelete = new IntArrayList();
                int nActuallyRemoved = 0;
                long bytesOnDisk = 0;
                synchronized (inputs) {
                    for (Input i : inputs.values()) {
                        if (i != null && !inputsToKeep.contains(i.id) && !i.isNew)
                            inputsToDelete.add(i.id);
                    }
                    IntIterator iter = inputsToDelete.intIterator();
                    LinkedList<Integer> retainForRecs = zest.getNewlyRecommendedInputsToQueue();
                    while (iter.hasNext()) {
                        int id = iter.next();
                        //Don't prune something if we haven't sent the hints out yet
                        if (retainForRecs.contains(Integer.valueOf(id)))
                            continue;
                        Input input = inputs.get(id);
                        inputs.remove(id);
                        input.evicted = true;
                        ConstraintRepresentation c = constraints.remove(input);
                        bytesOnDisk += c.destroy();
                        nActuallyRemoved++;
                    }
                }
                long end = System.currentTimeMillis();
                if(nActuallyRemoved > 0)
                    System.out.println("GC freed " + nActuallyRemoved + " inputs and " + bytesOnDisk + " bytes saved on disk in " + (end - start));
            }
        }
    }

    public Config getConfig() {
        return this.config;
    }

    public static final int EVICT_INPUTS_AFTER_THRESHOLD = 5000;

    public static class Input implements Externalizable {
        public int id;
        public byte[] bytes;
        public LinkedList<int[]> instructions;
        public boolean recommendedBefore;
        //We store the set of random requests from the original input - if we use Z3
        // to generate some hints, we'll need to position them using this
        public int[] requestsForRandom;
        //We might decide we are done with an input and don't want to explore it anymore, but will hang onto it for book keeping
        public boolean evicted;
        public HashSet<TargetedHint> targetedHints;
        boolean isNew;
        public double coveragePercentage;
        public long numExecutions;
        public LinkedList<StringHint[]> hints;
        public Integer score = 0;
        public boolean isValid;
        public LinkedList<StringHintGroup> hintGroups;

        public transient boolean isSentToKnarr;

        //Map from generator functions to the concrete values that we made.
        public transient HashMap<String, String> generatedStrings;

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
                out.writeInt(requestsForRandom.length);
                for(int i = 0; i < requestsForRandom.length; i++){
                    out.writeInt(requestsForRandom[i]);
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
            if(targetedHints == null){
                out.writeInt(-1);
            }else{
                out.writeInt(targetedHints.size());
                for(TargetedHint h : targetedHints){
                    out.writeObject(h);
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
            if (nReqs == -1) {
                this.requestsForRandom = null;
            } else {
                this.requestsForRandom = new int[nReqs];
                for (int i = 0; i < nReqs; i++) {
                    this.requestsForRandom[i] = in.readInt();
                }
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
            int nTargetedHints = in.readInt();
            if (nTargetedHints >= 0) {
                this.targetedHints = new HashSet<>(nTargetedHints);
                for (int i = 0; i < nTargetedHints; i++) {
                    this.targetedHints.add((TargetedHint) in.readObject());
                }
            }
        }

        public void addOrReplaceHint(StringHint hint, int[] insn) {
            if (this.instructions.isEmpty()) {
                this.instructions.add(insn);
                this.hints.add(new StringHint[]{hint});
                return;
            }
            Iterator<Coordinator.StringHint[]> newInputHintIter = this.hints.iterator();
            Iterator<int[]> newInputInsnIter = this.instructions.iterator();
            int pos = 0;
            boolean inserted = false;
            while(newInputInsnIter.hasNext()){
                newInputHintIter.next();
                int[] insns = newInputInsnIter.next();
                if(insns[0] == insn[0]){
                    inserted = true;
                    this.hints.set(pos, new Coordinator.StringHint[]{hint});
                    break;
                }
                if(insns[0] > insn[0]){
                    inserted = true;
                    this.hints.add(pos, new Coordinator.StringHint[]{hint});
                    this.instructions.add(pos, insn);
                    break;
                }
                pos++;
            }
            if(!inserted){
                this.hints.add(new Coordinator.StringHint[]{hint});
                this.instructions.add(insn);
            }
        }
    }

    public static abstract class TargetedHint implements Externalizable {

        private static final long serialVersionUID = 2196987482810090535L;

        @Override
        public void writeExternal(ObjectOutput out) throws IOException {

        }

        @Override
        public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {

        }

        public abstract void apply(ZestGuidance.Input newInput);
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

    public static class CharHint extends TargetedHint implements Externalizable{
        private static final long serialVersionUID = -4015984743755862044L;
        int hint;
        HintType type;
        int positionOfStringInInput;
        int lengthOfStringInInput;
        int offsetOfCharInString;
        String originalString;
        Branch targetedBranch;

        public CharHint(){

        }

        public CharHint(int hint, String originalString, HintType type, int positionOfStringInInput, int lengthOfStringInInput, int offsetOfCharInString, Branch targetedBranch) {
            this.hint = hint;
            this.type = type;
            this.positionOfStringInInput = positionOfStringInInput;
            this.lengthOfStringInInput = lengthOfStringInInput;
            this.offsetOfCharInString = offsetOfCharInString;
            this.originalString = originalString;
            this.targetedBranch = targetedBranch;
        }

        @Override
        public void writeExternal(ObjectOutput out) throws IOException {
            out.writeInt(hint);
            out.writeInt(type.ordinal());
            out.writeInt(positionOfStringInInput);
            out.writeInt(lengthOfStringInInput);
            out.writeInt(offsetOfCharInString);
            if(originalString == null)
                out.writeBoolean(false);
            else{
                out.writeBoolean(true);
                out.writeUTF(originalString);
            }
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            CharHint charHint = (CharHint) o;
            return hint == charHint.hint &&
                    positionOfStringInInput == charHint.positionOfStringInInput &&
                    lengthOfStringInInput == charHint.lengthOfStringInInput &&
                    offsetOfCharInString == charHint.offsetOfCharInString &&
                    type == charHint.type;
        }

        @Override
        public int hashCode() {
            return Objects.hash(hint, type, positionOfStringInInput, lengthOfStringInInput, offsetOfCharInString);
        }

        @Override
        public String toString() {
            return "CharHint{" +
                    "hint=" + hint +
                    ", type=" + type +
                    ", positionOfStringInInput=" + positionOfStringInInput +
                    ", lengthOfStringInInput=" + lengthOfStringInInput +
                    ", offsetOfCharInString=" + offsetOfCharInString +
                    ", originalString=" + originalString +
                    '}';
        }

        @Override
        public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
            this.hint = in.readInt();
            this.type = HintType.values()[in.readInt()];
            this.positionOfStringInInput = in.readInt();
            this.lengthOfStringInInput = in.readInt();
            this.offsetOfCharInString = in.readInt();
            if(in.readBoolean())
                this.originalString = in.readUTF();
        }

        @Override
        public void apply(ZestGuidance.Input parentInput) {
            //Look to see if we already have a string hint at this position, if so add this char at the right spot

            if(this.originalString == null) {
                return; //Should no longer occur...
            } else if (this.originalString.charAt(this.offsetOfCharInString) == this.hint) {
                return;
            }
            String newStr;
            if(this.offsetOfCharInString >= this.originalString.length())
                newStr = this.originalString + (char) this.hint;
            else if (this.offsetOfCharInString < 0)
                newStr = "" + (char) this.hint;
            else
                newStr = this.originalString.substring(0,this.offsetOfCharInString) + ((char) this.hint) + this.originalString.substring(this.offsetOfCharInString+1);
            StringHint newHint = new StringHint(newStr, HintType.CHAR, (Branch) null);

            if(newHint.hint.length() < MAXIMUM_STRING_EXTENDED_LENGTH){
                parentInput.stringEqualsHintsToTryInChildren.add(new StringHint[]{newHint, new StringHint(newHint.hint+'a', HintType.CHAR, (Branch) null)});
            }else{
                parentInput.stringEqualsHintsToTryInChildren.add(new StringHint[]{newHint});
            }
            parentInput.instructionsToTryInChildren.add(new int[]{this.positionOfStringInInput, this.lengthOfStringInInput});
        }
    }

    /**
     * A StringHint is a value that we want to try in a position in an input
     * There is a parallel vector that tracks where each hint goes.
     * StringHints are applied independently, unless they are part of a StringHintGroup
     */
    public static class StringHint implements Externalizable {
        private static final long serialVersionUID = -1812382770909515539L;
        public int priority;
        public String hint;
        public HintType type;
        public Branch targetBranch;
        transient String comparedString;

        public StringHint(){

        }

        public StringHint(String hint, HintType type, Branch targetBranch) {
            this.hint = hint;
            this.type = type;
            this.comparedString = hint;
            this.targetBranch = targetBranch;
        }

        public StringHint(String comparedString, String hint, HintType type, Branch targetBranch) {
            this.hint = hint;
            this.type = type;
            this.comparedString = comparedString;
            this.targetBranch = targetBranch;
        }


        public HintType getType() {
            return this.type;
        }

        public String getHint() {
            return this.hint;
        }

        public Branch getTargetBranch() {
            return targetBranch;
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
            String targetBranchStr = null;
            if(targetBranch != null){
                targetBranchStr = targetBranch.source;
            }
            return "StringHint{" +
                    "hint='" + hint + '\'' +
                    "hintLength=" + hint.length() +
                    ", type=" + type +
                    ", priority=" + priority +
                    ", branch=" + targetBranchStr +
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
            this.priority = in.readInt();
            this.targetBranch = (Branch) in.readObject();
        }

        @Override
        public void writeExternal(ObjectOutput out) throws IOException {
            out.writeUTF(this.hint);
            if(this.type == null){
                out.writeInt(-1);
            }else{
                out.writeInt(this.type.ordinal());
            }
            out.writeInt(this.priority);
            out.writeObject(this.targetBranch);
        }
    }
    public enum HintType {
        EQUALS,
        INDEXOF, //Currently we will also add a startsWith and an endsWith
        STARTSWITH,
        ENDSWITH,
        LENGTH,
        ISEMPTY,
        Z3,
        CHAR,
        GLOBAL_DICTIONARY
    }
    public static class Branch implements Externalizable {
        private static final long serialVersionUID = -6900391468143442577L;
        public int takenID, //For switches, `takenID` will be the switch ID, the same regarldess of whether it's taken or not.
                notTakenID;
        public boolean result, keep;
        public HashSet<Integer> controllingBytes;
        public String source = "";

        transient IntObjectHashMap<int[]> control;
        transient IntHashSet inputsTried;
        transient IntHashSet trueExplored;
        transient IntHashSet falseExplored;
        transient IntHashSet[] armsExplored;
        transient IntHashSet[] armsNotExplored;
        transient IntHashSet[] inputsTriedPerArm;
        transient boolean[] armsSolved;
        transient boolean isSolved;
        transient boolean isTimedOut;
        transient boolean isInFilter;


        public boolean isUsefulInputForNegation(Input input) {
            if (input == null || input.evicted)
                return false;
            if (!this.isSwitch()) {
                return !this.inputsTried.contains(input.id) &&
                        (this.trueExplored.contains(input.id) || this.falseExplored.contains(input.id));
            } else {
                for (int i = 0; i < armsExplored.length; i++) {
                    if (!armsSolved[i] && !this.inputsTriedPerArm[i].contains(input.id) && (
                            armsExplored[i].contains(input.id) || armsNotExplored[i].contains(input.id)))
                        return true;
                }
                return false;
            }
        }
        public boolean isSwitch(){
            return this.armsExplored != null;
        }
        public Branch(Coverage.CoverageData b) {
            this.result = b.taken;
            this.source = b.source;
            if (b instanceof Coverage.BranchData) {
                Coverage.BranchData branch = (Coverage.BranchData) b;
                this.takenID = branch.takenCode;
                this.notTakenID = branch.notTakenCode;
            } else if (b instanceof Coverage.SwitchData) {
                this.armsExplored = new IntHashSet[((Coverage.SwitchData) b).numArms + 1];
                this.armsNotExplored = new IntHashSet[((Coverage.SwitchData) b).numArms + 1];
                this.takenID = ((Coverage.SwitchData) b).switchID;
                this.armsExplored[((Coverage.SwitchData) b).arm] = new IntHashSet();
            } else {
                throw new UnsupportedOperationException();
            }
        }


        @Override
        public String toString() {
            if(this.armsSolved != null){
                return "Switch{" +
                        "takenID=" + takenID +
                        ", keep=" + keep +
                        ", source='" + source + '\'' +
                        ", armsExplored=" + Arrays.toString(armsExplored) +
                        ", armsNotExplored=" + Arrays.toString(armsNotExplored) +
                        ", inputsTriedPerArm=" + Arrays.toString(inputsTriedPerArm) +
                        ", armsSolved=" + Arrays.toString(armsSolved) +
                        ", isSolved=" + isSolved +
                        ", isTimedOut=" + isTimedOut +
                        '}';
            }
            return "Branch{" +
                    "takenID=" + takenID +
                    ", notTakenID=" + notTakenID +
                    ", source='" + source + '\'' +
                    ", trueExplored#=" + (trueExplored == null ? 0 : trueExplored.size())+
                    ", falseExplored#=" + (falseExplored == null ? 0 : falseExplored.size()) +
                    ", inputsTried#=" + (inputsTried == null ? 0 : inputsTried.size()) +
                    ", isTimedOut=" + isTimedOut +
                    ", isSolved=" + isSolved +
                    '}';
        }


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

        private int hash = -1;
        @Override
        public int hashCode() {
            if(hash == -1)
                hash = Objects.hash(takenID, notTakenID);
            return hash;
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

        public synchronized IntHashSet getInputsStillUseful() {
            IntHashSet ret = new IntHashSet();
            if(this.isSolved || this.isTimedOut)
                return ret;
            if(this.trueExplored != null)
                ret.addAll(this.trueExplored);
            if(this.falseExplored != null)
                ret.addAll(this.falseExplored);
            if(this.inputsTried != null)
                ret.removeAll(this.inputsTried);
            return ret;
        }

        public void evict(int inputID){
            if(this.isSwitch()){
                for(int i = 0; i < this.armsExplored.length; i++){
                    this.armsExplored[i].remove(inputID);
                    this.armsNotExplored[i].remove(inputID);
                }
            }else {
                this.trueExplored.remove(inputID);
                this.falseExplored.remove(inputID);
            }
        }

        static final int MAX_TIMES_SUGGEST_SAME_HINT = 1000 * 4; //each hint will be added 4 times, one for each byte in the source of randomnes, so this must be X4..
        transient ObjectIntHashMap<String> suggestedHints = new ObjectIntHashMap<>();
        public int addSuggestion(StringHint stringHint) {
            String hint = stringHint.comparedString;
            int rec = suggestedHints.getIfAbsentPut(hint, 0);
            suggestedHints.put(hint, rec + 1);
            return rec + 1;
        }

        private int branchCharHintsTried = 0;
        public boolean tryCharHint() {
            branchCharHintsTried++;
            int targetHints = 10;
            if(this.isSwitch())
                targetHints *= this.armsNotExplored.length;
            if(branchCharHintsTried <= targetHints)
                return true;
            return false;
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
        private boolean evicted;

        ConstraintRepresentation(LinkedList<Expression> e) {
            this.expr = e;
            this.exprFile = null;
        }
        ConstraintRepresentation(String exprFile) {
            this.expr = null;
            this.exprFile = exprFile;
        }


        private ConstraintDeserializer deserializer = new ConstraintDeserializer();
        private LinkedList<Expression> readConstraintsFromFile() {

            InputStream fileIn = null;
            try {
                //System.out.println("Reading constraints from " + this.exprFile);
                fileIn = new GZIPInputStream(new BufferedInputStream(new FileInputStream(this.exprFile)));
                return deserializer.fromInputStream(fileIn);
            } catch (IOException e) {
                e.printStackTrace();
                System.exit(-1); //TODO debugging
                return new LinkedList<Expression>();
            }
        }

        public LinkedList<Expression> getExpressions() {
            if(evicted)
                return new LinkedList<Expression>();
            return this.expr != null ? this.expr : readConstraintsFromFile();
        }

        public long destroy() {
            long ret = 0;
            if (this.exprFile != null) {
                Path p = Paths.get(this.exprFile);
                if (Files.exists(p)){
                    try {
                        ret = Files.size(p);
                        Files.delete(p);
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                }
            }
            this.expr = null;
            evicted = true;
            return ret;
        }
    }
}
