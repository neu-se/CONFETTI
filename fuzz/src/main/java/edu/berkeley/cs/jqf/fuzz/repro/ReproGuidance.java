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
package edu.berkeley.cs.jqf.fuzz.repro;

import java.io.*;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.function.Consumer;

import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.central.ZestClient;
import edu.berkeley.cs.jqf.fuzz.guidance.*;
import edu.berkeley.cs.jqf.fuzz.knarr.KnarrGuidance;
import edu.berkeley.cs.jqf.fuzz.util.Coverage;
import edu.berkeley.cs.jqf.instrument.tracing.events.BranchEvent;
import edu.berkeley.cs.jqf.instrument.tracing.events.CallEvent;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEvent;
import edu.columbia.cs.psl.phosphor.PreMain;
import edu.gmu.swe.knarr.runtime.PathUtils;
import org.jacoco.core.analysis.Analyzer;
import org.jacoco.core.analysis.CoverageBuilder;
import org.jacoco.core.tools.ExecFileLoader;
import org.jacoco.report.IReportVisitor;
import org.jacoco.report.csv.CSVFormatter;
import za.ac.sun.cs.green.expr.Expression;

/**
 * A front-end that provides a specified set of inputs for test
 * case reproduction,
 *
 * This class enables reproduction of a test case with an input file
 * generated by a guided fuzzing front-end such as AFL.
 *
 * @author Rohan Padhye
 */
public class ReproGuidance implements Guidance {
    private final File[] inputFiles;
    private final File traceDir;
    private int nextFileIdx = 0;
    private List<PrintStream> traceStreams = new ArrayList<>();
    private InputStream inputStream;
    private Coverage coverage = new Coverage();

    private Set<String> branchesCoveredInCurrentRun;
    private Set<String> allBranchesCovered;
    private boolean ignoreInvalidCoverage;

    private ZestClient central;
    private RecordingInputStream ris;

    HashMap<Integer, String> branchDescCache = new HashMap<>();
    private File currentInput;
    private KnarrGuidance.TaintingInputStream currentTaintingInputStream;


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
    public ReproGuidance(File[] inputFiles, File traceDir) {
        this.inputFiles = inputFiles;
        this.traceDir = traceDir;
        if (Boolean.getBoolean("jqf.repro.logUniqueBranches")) {
            allBranchesCovered = new HashSet<>();
            branchesCoveredInCurrentRun = new HashSet<>();
            ignoreInvalidCoverage = Boolean.getBoolean("jqf.repro.ignoreInvalidCoverage");

        }

        try {
            this.central = new ZestClient();
        } catch (IOException e) {
            this.central = null;
        }
    }

    /**
     * Constructs an instance of ReproGuidance with a single
     * input file to replay and a directory where the trace
     * events may be logged.
     *
     * @param inputFile an input file
     * @param traceDir an optional directory, which if non-null will
     *                 be the destination for log files containing event
     *                 traces
     */
    public ReproGuidance(File inputFile, File traceDir) {
        this(new File[]{inputFile}, traceDir);
    }

    /**
     * Returns an input stream corresponding to the next input file.
     *
     * @return an input stream corresponding to the next input file
     */
    @Override
    public InputStream getInput() {
            File inputFile = inputFiles[nextFileIdx];
            this.currentInput = inputFile;

            //CONFETTI: we changed the saved input format.
            try(ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(new FileInputStream(inputFile)))){
                int inputSize = ois.readInt();
                byte[] input = new byte[inputSize];
                ois.readFully(input);
                LinkedList<int[]> instructions = (LinkedList<int[]>) ois.readObject();
                LinkedList<Coordinator.StringHint[]> stringHints = (LinkedList<Coordinator.StringHint[]>) ois.readObject();
                LinkedList<Coordinator.TargetedHint> targetedHints = (LinkedList<Coordinator.TargetedHint>) ois.readObject();
                int offsetOfLastAppliedHint = ois.readInt();
                this.inputStream = new ByteArrayInputStream(input);
                KnarrGuidance.InputWithOnlyHints zestInput = new KnarrGuidance.InputWithOnlyHints();
                zestInput.instructions = instructions;
                zestInput.stringEqualsHints = stringHints;
                zestInput.appliedTargetedHints = targetedHints;
                System.out.println("Running: " + inputFile.getName());
                System.out.println("Input size: " + input.length);
                System.out.println("Hint count: " + stringHints.size());
                if(instructions != null && stringHints != null){
                    if(instructions.size() != stringHints.size())
                        throw new IllegalStateException();
                    this.inputStream = new StringEqualsHintingInputStream(this.inputStream, null, zestInput);
                }
                if(PreMain.RUNTIME_INST == true)
                {

                    this.currentTaintingInputStream = new KnarrGuidance.TaintingInputStream(this.inputStream);
                    this.inputStream = this.currentTaintingInputStream;
                }
            } catch (ClassNotFoundException e) {
                e.printStackTrace();
            } catch(IOException e){
                throw new GuidanceException("Failed to read " + inputFile, e);
            }

            if (central != null) {
                ris = new RecordingInputStream(this.inputStream);
                this.inputStream = ris;
            }

            if (allBranchesCovered != null) {
                branchesCoveredInCurrentRun.clear();
            }


            return this.inputStream;
    }

    /**
     * Returns <tt>true</tt> if there are more input files to replay.
     * @return <tt>true</tt> if there are more input files to replay
     */
    @Override
    public boolean hasInput() {
        return nextFileIdx < inputFiles.length;
    }

    /**
     * Returns the input file which is currently being repro'd.
     * @return the current input file
     */
    private File getCurrentInputFile() {
        return inputFiles[nextFileIdx];
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

        if (central != null) {
            //try {
            //    // Send new input / random requests used
            //    Boolean hintsUsed = StringEqualsHintingInputStream.hintUsedInCurrentInput;
            //    if (hintsUsed) {
            //        System.out.println("HINTS WERE USED IN CURRENT INPUT - SHOULD SEND THEM");
            //    }
            //    // TODO also replay String hints
            //    central.sendInput(ris.getRequests(), result, 0, new LinkedList<>(), 0.0, 0L, 0);
            //    StringEqualsHintingInputStream.hintUsedInCurrentInput = false;
            //
            //    // Send updated coverage
            //    central.sendCoverage(new Coverage());
            //} catch (IOException e) {
            //    throw new Error(e);
            //}
            throw new UnsupportedOperationException("Why is the central connected when you are doing repro? I don't know what that means. - JSB");
        }

        // Show errors for invalid tests
        if (result == Result.INVALID && error != null) {

            if(error != null ) {
                error.printStackTrace();
            }
            File inputFile = getCurrentInputFile();
            System.err.println(inputFile.getName() + ": Test run was invalid");
            // error.printStackTrace();
        }



        // Possibly accumulate coverage
        if (allBranchesCovered != null && (ignoreInvalidCoverage == false || result == Result.SUCCESS)) {
            assert branchesCoveredInCurrentRun != null;
            allBranchesCovered.addAll(branchesCoveredInCurrentRun);
        }

        // Maybe add to results csv
        if (traceDir != null) {
            File resultsCsv = new File(traceDir, "results.csv");
            boolean append = nextFileIdx > 0; // append for all but the first input
            try (PrintStream out = new PrintStream(new FileOutputStream(resultsCsv, append))) {
                String inputName = getCurrentInputFile().toString();
                String exception = result == Result.FAILURE ? error.getClass().getName() : "";
                out.printf("%s,%s,%s\n", inputName, result, exception);
            } catch (IOException e) {
                throw new GuidanceException(e);
            }
        }

        // Maybe checkpoint JaCoCo coverage
        String jacocoAccumulateJar = System.getProperty("jqf.repro.jacocoAccumulateJar");
        if (jacocoAccumulateJar != null) {
            String dir = System.getProperty("jqf.repro.jacocoAccumulateDir", ".");
            jacocoCheckpoint(new File(jacocoAccumulateJar), new File(dir));

        }

        // Increment file
        nextFileIdx++;


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
        if (branchesCoveredInCurrentRun != null) {
            return (e) -> {
                coverage.handleEvent(e);
                if (e instanceof BranchEvent) {
                    BranchEvent b = (BranchEvent) e;
                    int hash = b.getIid() * 31 + b.getArm();
                    String str = branchDescCache.get(hash);
                    if (str == null) {
                        str = String.format("(%09d) %s#%s():%d [%d]", b.getIid(), b.getContainingClass(), b.getContainingMethodName(),
                                b.getLineNumber(), b.getArm());
                        branchDescCache.put(hash, str);
                    }
                    branchesCoveredInCurrentRun.add(str);
                } else if (e instanceof CallEvent) {
                    CallEvent c = (CallEvent) e;
                    String str = branchDescCache.get(c.getIid());
                    if (str == null) {
                        str = String.format("(%09d) %s#%s():%d --> %s", c.getIid(), c.getContainingClass(), c.getContainingMethodName(),
                                c.getLineNumber(), c.getInvokedMethodName());
                        branchDescCache.put(c.getIid(), str);
                    }
                    branchesCoveredInCurrentRun.add(str);
                }
            };
        } else if (traceDir != null) {
            File traceFile = new File(traceDir, thread.getName() + ".log");
            try {
                PrintStream out = new PrintStream(traceFile);
                traceStreams.add(out);

                // Return an event logging callback
                return (e) -> {
                    coverage.handleEvent(e);
                    out.println(e);
                };
            } catch (FileNotFoundException e) {
                // Note the exception, but ignore trace events
                System.err.println("Could not open trace file: " + traceFile.getAbsolutePath());
            }
        }

        // If none of the above work, just update coverage
        return coverage::handleEvent;

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


    public void jacocoCheckpoint(File classFile, File csvDir) {
        int idx = nextFileIdx;
        csvDir.mkdirs();
        try {
            // Get exec data by dynamically calling RT.getAgent().getExecutionData()
            Class RT = Class.forName("org.jacoco.agent.rt.RT");
            Method getAgent = RT.getMethod("getAgent");
            Object agent = getAgent.invoke(null);
            Method dump = agent.getClass().getMethod("getExecutionData", boolean.class);
            byte[] execData = (byte[]) dump.invoke(agent, false);

            // Analyze exec data
            ExecFileLoader loader = new ExecFileLoader();
            loader.load(new ByteArrayInputStream(execData));
            final CoverageBuilder builder = new CoverageBuilder();
            Analyzer analyzer = new Analyzer(loader.getExecutionDataStore(), builder);
            analyzer.analyzeAll(classFile);

            // Generate CSV
            File csv = new File(csvDir, String.format("cov-%05d.csv", idx));
            try (FileOutputStream out = new FileOutputStream(csv)) {
                IReportVisitor coverageVisitor = new CSVFormatter().createVisitor(out);
                coverageVisitor.visitBundle(builder.getBundle("JQF"), null);
                coverageVisitor.visitEnd();
                out.flush();
            }


        } catch (Exception e) {
            System.err.println(e);
        }
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
