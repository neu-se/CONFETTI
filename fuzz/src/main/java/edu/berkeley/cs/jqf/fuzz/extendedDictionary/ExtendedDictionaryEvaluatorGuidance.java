/*
 * Copyright (c) 2017-2018 The Regents of the University of California
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package edu.berkeley.cs.jqf.fuzz.extendedDictionary;

import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.central.ZestClient;
import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance;
import edu.berkeley.cs.jqf.fuzz.guidance.*;
import edu.berkeley.cs.jqf.fuzz.util.Coverage;
import edu.berkeley.cs.jqf.instrument.tracing.SingleSnoop;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEvent;
import org.eclipse.collections.api.iterator.IntIterator;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.list.mutable.primitive.ShortArrayList;
import org.eclipse.collections.impl.map.mutable.primitive.IntObjectHashMap;

import java.io.*;
import java.util.*;
import java.util.function.Consumer;

public class ExtendedDictionaryEvaluatorGuidance implements Guidance {
    private final File[] inputFiles;
    private final File traceDir;
    private int nextFileIdx = 0;
    private List<PrintStream> traceStreams = new ArrayList<>();
    private InputStream inputStream;
    private Coverage coverage = new Coverage();

    private Set<String> branchesCoveredInCurrentRun;
    private Set<String> allBranchesCovered;
    private boolean ignoreInvalidCoverage;
    private Coverage runCoverage = new Coverage();
    public static final int NUM_TRIALS_PER_INPUT = System.getenv("TRIALS") == null ? 10 : Integer.parseInt(System.getenv("TRIALS"));


    private ZestClient central;
    private RecordingInputStream ris;

    HashMap<Integer, String> branchDescCache = new HashMap<>();
    private File currentInputFile;
    private ExtendedDictionaryLinearInput inputUnderAnalysis;
    public LinkedList<ExtendedDictionaryLinearInput> analyzedInputs = new LinkedList<>();
    private ZestGuidance.LinearInput currentInput;
    private PrintWriter logger;

    public String experimentName;
    public String appName;

    public void appendToLog(String str) {
        this.logger.println(str);
    }

    public void close() {
        if (this.inputUnderAnalysis != null)
            this.inputUnderAnalysis.logStats();
        if (this.traceDir != null)
            this.logger.close();
    }

    public static int generatedStrings = 0;

    class ExtendedDictionaryLinearInput extends ZestGuidance.LinearInput {
        Coverage coverage;
        int numTimesSelectedForFuzzing;

        int numChildrenSameCovAndCounts;
        int numChildrenSameCovLessCounts;
        int numChildrenLessCov;

        int numGlobalDictHintsWithRegularHintAlso;
        int numGlobalDictHintsWithoutRegularHintsAlso;
        int numStringHintsApplied;
        int numZ3HintsApplied;
        int numCharHintsApplied;
        int numHintsAvailable;
        int numHintPositionsAvailable;
        int maxHintsPerPosition = -1;
        int minHintsPerPosition = Integer.MAX_VALUE;
        int numStrings;

        IntArrayList indicesOfHintsThatAreGlobalDictionaryHints = new IntArrayList();

        //Allocate these lists once and reuse them for each child input
        private ShortArrayList mutatedArrayList;
        private LinkedList<int[]> nonGlobalDictInsns;
        private LinkedList<Coordinator.StringHint[]> nonGlobalDictHints;
        private int[] positionsToMutateInChildren;

        ExtendedDictionaryLinearInput(ZestGuidance.LinearInput other) {
            super(other);
            this.mutatedArrayList = new ShortArrayList(other.values.size());
            for (int i = 0; i < other.values.size(); i++) {
                this.mutatedArrayList.add(other.values.get(i));
            }

            this.parentInputIdx = other.parentInputIdx;
            this.numGlobalDictionaryHintsApplied = other.numGlobalDictionaryHintsApplied;
            if (other.allInstructions != null)
                this.allInstructions = new LinkedList<>(other.allInstructions);
            if (other.allStringEqualsHints != null)
                this.allStringEqualsHints = new LinkedList<>(other.allStringEqualsHints);

            this.organizeHintsByPosition();
            for (int i = 0; i < this.stringEqualsHints.size(); i++) {
                if (this.stringEqualsHints.get(i)[0].type == Coordinator.HintType.GLOBAL_DICTIONARY) {
                    indicesOfHintsThatAreGlobalDictionaryHints.add(i);
                    //Is there also a regular string hint here for the same value?
                    int[] pos = this.instructions.get(i);
                    String val = this.stringEqualsHints.get(i)[0].hint;
                    if (hintsAtOffsets.containsKey(pos[0])) {
                        boolean found = false;
                        for (Coordinator.StringHint h : hintsAtOffsets.get(pos[0])) {
                            if (h.getType() != Coordinator.HintType.GLOBAL_DICTIONARY && h.getHint().equals(val)) {
                                this.numGlobalDictHintsWithRegularHintAlso++;
                                found = true;
                            }
                        }
                        if (!found)
                            this.numGlobalDictHintsWithoutRegularHintsAlso++;
                    } else {
                        this.numGlobalDictHintsWithoutRegularHintsAlso++;
                    }
                } else if (this.stringEqualsHints.get(i)[0].type == Coordinator.HintType.Z3) {
                    this.numZ3HintsApplied++;
                } else if (this.stringEqualsHints.get(i)[0].type == Coordinator.HintType.CHAR) {
                    this.numCharHintsApplied++;
                } else {
                    this.numStringHintsApplied++;
                }
            }
            indicesOfHintsThatAreGlobalDictionaryHints.reverseThis();
            this.nonGlobalDictHints = new LinkedList<>(this.stringEqualsHints);
            this.nonGlobalDictInsns = new LinkedList<>(this.instructions);
            this.positionsToMutateInChildren = new int[indicesOfHintsThatAreGlobalDictionaryHints.size()];
            IntIterator iter = indicesOfHintsThatAreGlobalDictionaryHints.intIterator();
            int i = 0;
            while (iter.hasNext()) {
                int hintToRemove = iter.next();
                this.nonGlobalDictHints.remove(hintToRemove);
                int[] pos = this.nonGlobalDictInsns.remove(hintToRemove);
                this.positionsToMutateInChildren[i] = pos[0];
                i++;
            }
        }

        public void logStats() {
            //("inputIdx,seedSource,parentInputIdx,inputSizeBytes,numStringsTotal,numGlobalDictHints,numCharHints,numStringHints,
            // numZ3Hints,numHintsAvailable,numHintPositionsAvailable,minHintsPerPosition,
            // maxHintsPerPosition,numGlobalDictHintsWithRegularHintAlso,
            // numGlobalDictHintsWithoutRegularHintsAlso,numChildrenSameCovAndCounts,
            // numChildrenSameCovLessCounts,numChildrenLessCov");
            if (this.maxHintsPerPosition < 0)
                this.maxHintsPerPosition = 0;
            if (this.minHintsPerPosition == Integer.MAX_VALUE)
                this.minHintsPerPosition = 0;
            appendToLog(String.format("%s,%s,%d,%s,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d",
                    appName,
                    experimentName,
                    this.id,
                    this.seedSource.toString(),
                    this.parentInputIdx,
                    this.values.size(),
                    this.numStrings,
                    this.indicesOfHintsThatAreGlobalDictionaryHints.size(),
                    this.numCharHintsApplied,
                    this.numStringHintsApplied,
                    this.numZ3HintsApplied,
                    this.numHintsAvailable,
                    this.numHintPositionsAvailable,
                    this.minHintsPerPosition,
                    this.maxHintsPerPosition,
                    this.numGlobalDictHintsWithRegularHintAlso,
                    this.numGlobalDictHintsWithoutRegularHintsAlso,
                    this.numChildrenSameCovAndCounts,
                    this.numChildrenSameCovLessCounts,
                    this.numChildrenLessCov));
            //Reduce memory pressure by allowing this all to be freed...
            this.coverage = null;
            this.nonGlobalDictHints = null;
            this.nonGlobalDictInsns = null;
            this.stringEqualsHints = null;
            this.instructions = null;
        }

        private IntObjectHashMap<ArrayList<Coordinator.StringHint>> hintsAtOffsets;

        private void organizeHintsByPosition() {
            hintsAtOffsets = new IntObjectHashMap<>();
            if (this.allInstructions == null)
                return;
            Iterator<int[]> insnIter = allInstructions.iterator();
            Iterator<Coordinator.StringHint[]> hintIter = allStringEqualsHints.iterator();
            while (insnIter.hasNext()) {
                int[] insn = insnIter.next();
                Coordinator.StringHint[] hints = hintIter.next();
                if (!hintsAtOffsets.containsKey(insn[0])) {
                    hintsAtOffsets.put(insn[0], new ArrayList<>());
                }
                for (Coordinator.StringHint hint : hints) {
                    if (hint.getType() != Coordinator.HintType.GLOBAL_DICTIONARY)
                        hintsAtOffsets.get(insn[0]).add(hint);
                }
            }
            IntIterator allHintsIter = hintsAtOffsets.keysView().intIterator();
            while (allHintsIter.hasNext()) {
                int pos = allHintsIter.next();
                ArrayList<Coordinator.StringHint> hints = hintsAtOffsets.get(pos);
                this.numHintsAvailable += hints.size();
                if (hints.size() > 0)
                    this.numHintPositionsAvailable++;
                if (hints.size() > this.maxHintsPerPosition)
                    this.maxHintsPerPosition = hints.size();
                if (hints.size() < this.minHintsPerPosition)
                    this.minHintsPerPosition = hints.size();
            }
        }


        private ZestGuidance.LinearInput childInput;
        @Override
        public ZestGuidance.Input fuzz(Random random) {
            // Create a new input that is the same as this one, but with the hints removed, and the corresponding input bytes
            // replaced to pick something at random from the dictionary
            if (this.childInput == null) {
                childInput = new ZestGuidance.LinearInput();
                childInput.values = this.mutatedArrayList;
                childInput.stringEqualsHints = this.nonGlobalDictHints;
                childInput.instructions = this.nonGlobalDictInsns;
            } else {
                childInput.reset();
            }
            for (int i = 0; i < this.positionsToMutateInChildren.length; i++) {
                int pos = this.positionsToMutateInChildren[i];
                childInput.values.set(pos - 1, (short) 0);
                int newChoice = random.nextInt();
                if (newChoice < 0)
                    newChoice = 0 - newChoice;
                childInput.values.set(pos, (byte) newChoice);
                childInput.values.set(pos + 1, (byte) (newChoice >> 8));
                childInput.values.set(pos + 2, (byte) (newChoice >> 16));
                childInput.values.set(pos + 3, (byte) (newChoice >> 24));
            }
            numTimesSelectedForFuzzing++;
            return childInput;
        }

        public boolean hasInputsToTry() {
            if (this.numChildrenSameCovAndCounts > 0)
                return false;
            if (!this.indicesOfHintsThatAreGlobalDictionaryHints.isEmpty() && numTimesSelectedForFuzzing < NUM_TRIALS_PER_INPUT)
                return true;
            return false;
        }
    }

    long startTime;
    long executions;

    /**
     * Constructs an instance of ReproGuidance with a list of
     * input files to replay and a directory where the trace
     * events may be logged.
     *
     * @param inputFiles a list of input files
     * @param traceDir an optional directory, which if non-null will
     *                 be the destination for log files containing event
     *                 traces
     */
    public ExtendedDictionaryEvaluatorGuidance(File[] inputFiles, File traceDir) {
        this.inputFiles = inputFiles;
        this.traceDir = traceDir;

        this.startTime = System.currentTimeMillis();

        String appName = System.getenv("APP_NAME");
        String expName = System.getenv("EXP_NAME");
        if (appName != null)
            this.appName = appName;
        else
            this.appName = "";
        if (expName != null)
            this.experimentName = expName;
        else
            this.experimentName = "";

        SingleSnoop.setCoverageListener(runCoverage);
        if (Boolean.getBoolean("jqf.repro.logUniqueBranches")) {
            allBranchesCovered = new HashSet<>();
            branchesCoveredInCurrentRun = new HashSet<>();
            ignoreInvalidCoverage = Boolean.getBoolean("jqf.repro.ignoreInvalidCoverage");

        }

        try {
            if (this.traceDir != null) {
                this.logger = new PrintWriter(new FileWriter(traceDir));
                appendToLog("app,experiment,inputIdx,seedSource,parentInputIdx,inputSizeBytes,numStringsTotal,numGlobalDictHints,numCharHints,numStringHints,numZ3Hints,numHintsAvailable,numHintPositionsAvailable,minHintsPerPosition,maxHintsPerPosition,numGlobalDictHintsWithRegularHintAlso,numGlobalDictHintsWithoutRegularHintsAlso,numChildrenSameCovAndCounts,numChildrenSameCovLessCounts,numChildrenLessCov");
            } else {
                this.logger = new PrintWriter(System.out);
            }
            this.central = new ZestClient();
        } catch (IOException e) {
            this.central = null;
        }
    }

    private Random random = new Random();

    /**
     * Returns an input stream corresponding to the next input file.
     *
     * @return an input stream corresponding to the next input file
     */
    @Override
    public InputStream getInput() {
        runCoverage.clear();
        generatedStrings = 0;
        executions++;
        if (this.inputUnderAnalysis != null && this.inputUnderAnalysis.hasInputsToTry()) {
            currentInput = (ZestGuidance.LinearInput) inputUnderAnalysis.fuzz(random);
        } else {
            if (this.inputUnderAnalysis != null)
                this.inputUnderAnalysis.logStats();

            if(nextFileIdx % 100 == 0){
                int speed = (int) (1000*executions / (System.currentTimeMillis() - startTime));
                System.out.println("Status: " + nextFileIdx + "/" + inputFiles.length + " seeds evaluated, " + executions + " executions, at " + speed + " execs/sec");
            }

            File inputFile = inputFiles[nextFileIdx];
            nextFileIdx++;
            this.currentInputFile = inputFile;
            try {
                ZestGuidance.LinearInput linearInput = ZestGuidance.LinearInput.fromFile(inputFile);
                this.inputUnderAnalysis = new ExtendedDictionaryLinearInput(linearInput);
                this.inputUnderAnalysis.id = Integer.parseInt(inputFile.getName().substring(3));
                this.analyzedInputs.add(inputUnderAnalysis);
                currentInput = inputUnderAnalysis;
            } catch (IOException | ClassNotFoundException e) {
                e.printStackTrace();
                throw new GuidanceException(e);
            }
        }
        InputStream is = new InputStream() {
            int bytesRead = 0;

            @Override
            public int read() throws IOException {

                ZestGuidance.LinearInput linearInput = currentInput;
                // Attempt to get a value from the list, or else generate a random value
                int ret = linearInput.getOrGenerateFresh(bytesRead++, random);
                // infoLog("read(%d) = %d", bytesRead, ret);
                return ret;

            }
        };
        if ((currentInput.stringEqualsHints != null))
            is = new StringEqualsHintingInputStream(is, ris, currentInput);

        if (allBranchesCovered != null) {
            branchesCoveredInCurrentRun.clear();
        }
        return is;
    }

    /**
     * Returns <tt>true</tt> if there are more input files to replay.
     * @return <tt>true</tt> if there are more input files to replay
     */
    @Override
    public boolean hasInput() {
        if (this.inputUnderAnalysis != null && this.inputUnderAnalysis.hasInputsToTry())
            return true;
        return nextFileIdx < inputFiles.length;
    }

    /**
     * Returns the input file which is currently being repro'd.
     * @return the current input file
     */
    private File getCurrentInputFile() {
        return currentInputFile;
    }

    /**
     * Logs the end of run in the log files, if any.
     *
     * @param result   the result of the fuzzing trial
     * @param error    the error thrown during the trial, or <tt>null</tt>
     */
    @Override
    public void handleResult(Result result, Throwable error) {
        // Close the open input file
        try {
            if (inputStream != null) {
                inputStream.close();
            }
        } catch (IOException e) {
            throw new GuidanceException(e);
        }
        runCoverage.lock();
        if (this.currentInput == this.inputUnderAnalysis) {
            //We just ran the input as-is, record the coverage!
            this.inputUnderAnalysis.coverage = new Coverage(runCoverage);
            this.inputUnderAnalysis.numStrings = generatedStrings;
        } else {
            //Fuzzed version, see if coverage is same or not
            Coverage.CoverageComparisonResult res = this.inputUnderAnalysis.coverage.compareCoverage(runCoverage);
            if (res == Coverage.CoverageComparisonResult.THAT_COVERS_ALL_OF_THIS)
                this.inputUnderAnalysis.numChildrenSameCovLessCounts++;
            else if (res == Coverage.CoverageComparisonResult.THAT_COVERS_ALL_OF_THIS_SAME_OR_GREATER_HITS)
                this.inputUnderAnalysis.numChildrenSameCovAndCounts++;
            else
                this.inputUnderAnalysis.numChildrenLessCov++;
        }
        runCoverage.unlock();
    }

    /**
     * Returns a callback that can log trace events or code coverage info.
     *
     * <p>If the system property <tt>jqf.repro.logUniqueBranches</tt> was
     * set to <tt>true</tt>, then the callback collects coverage info into
     * the set {@link #branchesCoveredInCurrentRun}, which can be accessed using
     * {@link #getBranchesCovered()}.</p>
     *
     * <p>Otherwise, if the <tt>traceDir</tt> was non-null during the construction of
     * this Guidance instance, then one log file per thread of
     * execution is created in this directory. The callbacks generated
     * by this method write trace event descriptions in sequence to
     * their own thread's log files.</p>
     *
     * <p>If neither of the above are true, the returned callback simply updates
     * a total coverage map (see {@link #getCoverage()}.</p>
     *
     * @param thread the thread whose events to handle
     * @return a callback to log code coverage or execution traces
     */
    @Override
    public Consumer<TraceEvent> generateCallBack(Thread thread) {
        if (thread.getName().endsWith("main")) {
            return this::handleEvent;
        } else return this.emptyEvent;
    }

    private Consumer<TraceEvent> emptyEvent = new Consumer<TraceEvent>() {
        @Override
        public void accept(TraceEvent traceEvent) {

        }
    };

    private void handleEvent(TraceEvent e) {
        // Collect totalCoverage
        runCoverage.handleEvent(e);
    }


    /**
     * Returns a reference to the coverage statistics.
     * @return a reference to the coverage statistics
     */
    public Coverage getCoverage() {
        return coverage;
    }


    /**
     * Retyrns the set of branches covered by this repro.
     *
     * <p>This set will only be non-empty if the system
     * property <tt>jqf.repro.logUniqueBranches</tt> was
     * set to <tt>true</tt> before the guidance instance
     * was constructed.</p>
     *
     * <p>The format of each element in this set is a
     * custom format that strives to be both human and
     * machine readable.</p>
     *
     * <p>A branch is only logged for inputs that execute
     * successfully. In particular, branches are not recorded
     * for failing runs or for runs that violate assumptions.</p>
     *
     * @return the set of branches covered by this repro
     */
    public Set<String> getBranchesCovered() {
        return allBranchesCovered;
    }


    @Override
    public void setArgs(Object[] args) {
        //if(PreMain.RUNTIME_INST){
        //    Expression constraints = PathUtils.getCurPC().constraints;
        //    HashSet<Integer> choiceVars = KnarrGuidance.extractVarNames(constraints);
        //    LinkedList<int[]> rangesUsedInControlPointsInGenerator = new LinkedList<>();
        //
        //    for(int[] requestForRandomBytes : this.currentTaintingInputStream.readRequests){
        //        boolean fullRequestMatched = false;
        //        int offsetsMatched = 0;
        //        if(requestForRandomBytes[1] != 1)
        //            continue; //TODO testing with only booleans
        //        for(int i = requestForRandomBytes[0]; i< requestForRandomBytes[0] + requestForRandomBytes[1]; i++){
        //            if(choiceVars.contains(i)){
        //                offsetsMatched++;
        //            }
        //        }
        //        if(offsetsMatched == requestForRandomBytes[1]){
        //            // The entire request matched
        //            rangesUsedInControlPointsInGenerator.add(requestForRandomBytes);
        //        }else{
        //            // Only part of the request matched, add each byte one-by-one
        //            for(int i = requestForRandomBytes[0]; i< requestForRandomBytes[0] + requestForRandomBytes[1]; i++){
        //                if (choiceVars.contains(i)) {
        //                    rangesUsedInControlPointsInGenerator.add(new int[]{i, 1});
        //                }
        //            }
        //        }
        //    }
        //    for (int[] each : rangesUsedInControlPointsInGenerator) {
        //        System.out.println("TARGET: " + each[0] + "..." + (each[0] + each[1]));
        //    }
        //}
    }

}
