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
package edu.berkeley.cs.jqf.fuzz.ei;

import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.central.ZestClient;
import edu.berkeley.cs.jqf.fuzz.ei.ExecutionIndex.Prefix;
import edu.berkeley.cs.jqf.fuzz.ei.ExecutionIndex.Suffix;
import edu.berkeley.cs.jqf.fuzz.guidance.*;
import edu.berkeley.cs.jqf.fuzz.util.Coverage;
import edu.berkeley.cs.jqf.fuzz.util.ProducerHashMap;
import edu.berkeley.cs.jqf.instrument.tracing.SingleSnoop;
import edu.berkeley.cs.jqf.instrument.tracing.events.CallEvent;
import edu.berkeley.cs.jqf.instrument.tracing.events.ReturnEvent;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEvent;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEventVisitor;
import edu.columbia.cs.psl.phosphor.struct.IntSinglyLinkedList;
import org.apache.bcel.classfile.JavaClass;
import org.eclipse.collections.api.iterator.IntIterator;
import org.eclipse.collections.api.iterator.ShortIterator;
import org.eclipse.collections.api.list.primitive.IntList;
import org.eclipse.collections.impl.list.mutable.primitive.ByteArrayList;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.list.mutable.primitive.ShortArrayList;
import org.eclipse.collections.impl.set.mutable.primitive.IntHashSet;
import org.paukov.combinatorics3.Generator;
import org.w3c.dom.Document;

import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import java.io.*;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryMXBean;
import java.time.Duration;
import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import static java.lang.Math.ceil;
import static java.lang.Math.log;

/**
 * A guidance that performs coverage-guided fuzzing using two coverage maps,
 * one for all inputs and one for valid inputs only.
 *
 * @author Rohan Padhye
 */
public class ZestGuidance implements Guidance, TraceEventVisitor {

    // Currently, we only support single-threaded applications
    // This field is used to ensure that
    private Thread appThread;

    /** The last event handled by this guidance */
    private TraceEvent lastEvent;

    /** The execution indexing logic. */
    private ExecutionIndexingState eiState;

    /** A pseudo-random number generator for generating fresh values. */
    private Random random = new Random();

    /** The name of the test for display purposes. */
    private final String testName;

    // ------------ ALGORITHM BOOKKEEPING ------------

    private int combinationsLimit = Integer.MAX_VALUE;

    /** The max amount of time to run for, in milli-seconds */
    private final long maxDurationMillis;

    /** The number of trials completed. */
    private long numTrials = 0;

    /** The number of valid inputs. */
    private long numValid = 0;

    /** The directory where fuzzing results are written. */
    private final File outputDirectory;

    /** The directory where saved inputs are written. */
    private File savedInputsDirectory;

    /** The directory where saved inputs are written. */
    private File savedFailuresDirectory;

    /** Set of saved inputs to fuzz. */
    private ArrayList<Input> savedInputs = new ArrayList<>();

    // CONFETTI book-keeping
    private long[] countOfInputsSavedByMutation = new long[MutationType.values().length];
    private long[] countOfInputsCreatedByMutation = new long[MutationType.values().length];

    private long[] countOfSavedInputsBySeedSource = new long[SeedSource.values().length];
    private long[] countOfFailingInputsBySeedSource = new long[SeedSource.values().length];

    private static int[] countOfInputsSavedWithMutationCountsRanges = new int[]{0, 1, 5, 10, 20, 100, 1000, 10000};

    private long[] countOfInputsSavedWithMutationCounts = new long[countOfInputsSavedWithMutationCountsRanges.length];
    private static long[] countOfInputsCreatedWithMutationCounts = new long[countOfInputsSavedWithMutationCountsRanges.length];

    private long[] countOfInputsSavedWithHintMutationCounts = new long[countOfInputsSavedWithMutationCountsRanges.length];
    private static long[] countOfInputsCreatedWithHintMutationCounts = new long[countOfInputsSavedWithMutationCountsRanges.length];

    public long countOfSavedInputsWithExtendedDictionaryHints;
    public long countOfCreatedInputsWithExtendedDictionaryHints;


    /**
     * If the central says that there is a recommendation for something, it will jump up to the front here
     */
    private LinkedList<Integer> recommendedInputsToFuzz = new LinkedList<>();
    private IntHashSet inputsWithHintsAtStartOfCycle = new IntHashSet();
    /**
     * COFNETTI:
     * If true, then while fuzzing, Zest will check for hints on inputs that were recently generated, adn if they exist,
     * jump back to re-fuzz those.
     *
     * If false, then Zest will only fetch hints at the start of a fuzzing cycle: meaning that hints won't be applied for an input
     * until, at the soonest, the next fuzzing cycle.
     */
    private static final boolean FETCH_HINTS_MID_CYCLE = true;

    /**
     * CONFETTI:
     * If true, then a parent that would normally get N mutations when fuzzed will now get N + Math.min(N, numHints) mutations -
     * allowing for Math.min(N, numHints) hints to be applied, in *addition* to regular mutatinos.
     *
     * If false, then a parent that would normally get N mutations when fuzzed will still get N, and some random fraction of those
     * will be applying a single hint (until the hints are exhausted).
     *
     * Does not impact the application of multiple hints simultaneously.
     */
    private static final boolean INCLUDE_SINGLE_HINTS_AS_BONUS_MUTATIONS = false;

    private PriorityQueue<Input> savedInputsAccess = new PriorityQueue<Input>(new InputComparator());

    private class InputComparator implements Comparator<Input> {
        public int compare(Input i1, Input i2)
        {
            if (i1.score < i2.score)
                return 1;
            else if (i1.score > i2.score)
                return -1;
            return 0;
        }
    }

    public static PriorityQueueConfig priorityQueueConfig;

    public static boolean IGNORE_GLOBAL_DICTIONARY = System.getenv("NO_GLOBAL_DICT") != null;

    static {
        try {

            Properties p = new Properties();
            String priorityFile = System.getProperty("priority");
            if (priorityFile != null) {
                p.load(new BufferedReader(new FileReader(new File(System.getProperty("priority")))));
            } else {
                p.load(ZestDriver.class.getResourceAsStream("/PriorityQueue.properties"));
            }
            priorityQueueConfig = new PriorityQueueConfig(p);
        } catch (IOException e) {
            throw new Error(e);
        }
    }

    public static class PriorityQueueConfig {

        public interface Arithmetic {
            int operation(int a, int b);
        }

        public final boolean usePriorityQueue;

        public  HashMap<String, Arithmetic> operations  = new HashMap<>();


        public final int validInputScoreValue;

        public final Arithmetic validInputScoreOperation;

        public final int  favoredInputScoreValue;

        public final Arithmetic favoredInputScoreOperation;

        public final int z3HintScoreValue;

        public final Arithmetic z3HintScoreOperation;

        public final int equalsHintScoreValue;

        public final Arithmetic equalsHintScoreOperation;

        public final int z3newBranchesScoreValue;

        public final Arithmetic  z3newBranchesScoreOperation;

        public  PriorityQueueConfig(Properties p) {

            operations.put("+", (int a, int b) -> (a + b));
            operations.put("-", (int a, int b) -> (a - b));
            operations.put("/", (int a, int b) -> (a / b));
            operations.put("*", (int a, int b) -> (a * b));


            usePriorityQueue = (p.getProperty("usePriorityQueue") != null);


            String validInputScoreCalculation = p.getProperty("validInputScoreCalculation");
            if(validInputScoreCalculation != null) {
                validInputScoreValue = Integer.parseInt(validInputScoreCalculation.split(",")[1]);
                validInputScoreOperation = operations.get(validInputScoreCalculation.split(",")[0]);
            } else {
                validInputScoreValue = 0;
                validInputScoreOperation = operations.get("+");
            }

            String favoredInputScoreCalculation = p.getProperty("favoredInputScoreCalculation");
            if(validInputScoreCalculation != null) {
                favoredInputScoreValue = Integer.parseInt(favoredInputScoreCalculation.split(",")[1]);
                favoredInputScoreOperation = operations.get(favoredInputScoreCalculation.split(",")[0]);
            } else {
                favoredInputScoreValue = 0;
                favoredInputScoreOperation = operations.get("+");
            }


            String z3HintScoreCalculation = p.getProperty("z3HintScoreCalculation");
            if(validInputScoreCalculation != null) {
                z3HintScoreValue = Integer.parseInt(z3HintScoreCalculation.split(",")[1]);
                z3HintScoreOperation = operations.get(z3HintScoreCalculation.split(",")[0]);
            } else {
                z3HintScoreValue = 0;
                z3HintScoreOperation = operations.get("+");
            }


            String equalsHintScoreCalculation = p.getProperty("equalsHintScoreCalculation");
            if(validInputScoreCalculation != null) {
                equalsHintScoreValue = Integer.parseInt(equalsHintScoreCalculation.split(",")[1]);
                equalsHintScoreOperation = operations.get(z3HintScoreCalculation.split(",")[0]);
            } else {
                equalsHintScoreValue = 0;
                equalsHintScoreOperation = operations.get("+");
            }

            String z3newBranchesScoreCalculation = p.getProperty("z3newBranchesScoreCalculation");
            if(validInputScoreCalculation != null) {
                z3newBranchesScoreValue = Integer.parseInt(equalsHintScoreCalculation.split(",")[1]);
                z3newBranchesScoreOperation = operations.get(z3HintScoreCalculation.split(",")[0]);
            } else {
                z3newBranchesScoreValue = 0;
                z3newBranchesScoreOperation = operations.get("+");
            }
        }
    }



    /** Queue of seeds to fuzz. */
    private Deque<SeedInput> seedInputs = new ArrayDeque<>();

    /** Current input that's running -- valid after getInput() and before handleResult(). */
    public static Input<?> currentInput;

    /** Index of currentInput in the savedInputs -- valid after seeds are processed (OK if this is inaccurate). */
    private int currentParentInputIdx = 0;

    /**
     * We might jump around in terms of "currentParentInputIdx", but still need to know where we were last in a
     * cycle working thorugh the list. This variable will always track the last input idx that was selected by zest, not
     * any that was from CONFETTI. NB an input might be selected for fuzzing multiple times within the same fuzzing cycle.
     */
    private int currentParentInputCounter = 0;


    /** Keep track of whether or not we have exhausted hints for the current input **/
    private boolean currentParentExhaustedHints = false;


    private long z3ThreadStartedInputNum = -1L;

    /** Number of mutated inputs generated from currentInput. */
    private int numChildrenGeneratedForCurrentParentInput = 0;

    /** CONFETTI: Number of mutated inputs generated from currentInput at the most recent directed mutation location. */
    private int numChildrenGeneratedForCurrentMutationLocation = 0;


    /** Number of cycles completed (i.e. how many times we've reset currentParentInputIdx to 0. */
    private int cyclesCompleted = 0;

    /** Number of favored inputs in the last cycle. */
    private int numFavoredLastCycle = 0;

    /** Number of saved inputs.
     *
     * This is usually the same as savedInputs.size(),
     * but we do not really save inputs in TOTALLY_RANDOM mode.
     */
    private int numSavedInputs = 0;

    /** Coverage statistics for a single run. */
    private Coverage runCoverage = new Coverage();

    /** Cumulative coverage statistics. */
    private Coverage totalCoverage = new Coverage();

    /** Cumulative coverage for valid inputs. */
    private Coverage validCoverage = new Coverage();

    /** The maximum number of keys covered by any single input found so far. */
    private int maxCoverage = 0;


    private int heartbeatInterval = 1000;

    /** A mapping of coverage keys to inputs that are responsible for them. */
    private Map<Object, Input> responsibleInputs = new HashMap<>(totalCoverage.size());

    /** The set of unique failures found so far. */
    private Set<List<StackTraceElement>> uniqueFailures = new HashSet<>();

    /**
     * A map of execution contexts (call stacks) to locations in saved inputs with those contexts.
     *
     * This is a nifty data structure for quickly finding candidates for input splicing.
     */
    private Map<ExecutionContext, ArrayList<InputLocation>> ecToInputLoc
            = new ProducerHashMap<>(() -> new ArrayList<>());

    // ---------- LOGGING / STATS OUTPUT ------------

    /** Whether to print log statements to stderr (debug option; manually edit). */
    private static final boolean verbose = false;


    /** A system console, which is non-null only if STDOUT is a console. */
    private final Console console = System.console();

    /** Time since this guidance instance was created. */
    private final Date startTime = new Date();

    /** Time at last stats refresh. */
    private Date lastRefreshTime = startTime;

    /** Total execs at last stats refresh. */
    private long lastNumTrials = 0;

    /** Minimum amount of time (in millis) between two stats refreshes. */
    private static final long STATS_REFRESH_TIME_PERIOD = Integer.getInteger("ZEST_STATS_REFRESH_TIME_PERIOD", 300);;

    /** The file where log data is written. */
    private static File logFile;

    /** The file where saved plot data is written. */
    private File statsFile;

    /** Whether to hide fuzzing statistics **/
    protected final boolean QUIET_MODE = Boolean.getBoolean("jqf.ei.QUIET_MODE");

    private Consumer<TraceEvent> emptyEvent = new Consumer<TraceEvent>() {
        @Override
        public void accept(TraceEvent traceEvent) {

        }
    };
    /** The currently executing input (for debugging purposes). */
    private File currentInputFile;

    /** Whether to print the fuzz config to the stats screen. */
    private static boolean SHOW_CONFIG = true;

    // ------------- TIMEOUT HANDLING ------------

    /** Timeout for an individual run. */
    private long singleRunTimeoutMillis;

    /** Date when last run was started. */
    private Date runStart;

    /** Number of conditional jumps since last run was started. */
    private long branchCount;




    // ------------- FUZZING HEURISTICS ------------

    /** Turn this on to disable all guidance (i.e. no mutations, only random fuzzing) */
    static final boolean TOTALLY_RANDOM = Boolean.getBoolean("jqf.ei.TOTALLY_RANDOM");

    /** Whether to use real execution indexes as opposed to flat numbering. */
    static final boolean DISABLE_EXECUTION_INDEXING = !Boolean.getBoolean("jqf.ei.ENABLE_EXECUTION_INDEXING");

    /** Whether to save only valid inputs **/
    static final boolean SAVE_ONLY_VALID = Boolean.getBoolean("jqf.ei.SAVE_ONLY_VALID");

    /** Max input size to generate. */
    public static int MAX_INPUT_SIZE = Integer.getInteger("jqf.ei.MAX_INPUT_SIZE", 10240);

    /** Whether to generate EOFs when we run out of bytes in the input, instead of randomly generating new bytes. **/
    static final boolean GENERATE_EOF_WHEN_OUT = Boolean.getBoolean("jqf.ei.GENERATE_EOF_WHEN_OUT");

    /** Baseline number of mutated children to produce from a given parent input. */
    static final int NUM_CHILDREN_BASELINE = 50;

    /** Multiplication factor for number of children to produce for favored inputs. */
    static final int NUM_CHILDREN_MULTIPLIER_FAVORED = 20;

    /** Mean number of mutations to perform in each round. */
    static final double MEAN_MUTATION_COUNT = 8.0;

    /** Mean number of contiguous bytes to mutate in each mutation. */
    static final double MEAN_MUTATION_SIZE = 4.0; // Bytes

    /** Max number of contiguous bytes to splice in from another input during the splicing stage. */
    static final int MAX_SPLICE_SIZE = 64; // Bytes

    /** Whether to splice only in the same sub-tree */
    static final boolean SPLICE_SUBTREE = Boolean.getBoolean("jqf.ei.SPLICE_SUBTREE");

    /** Whether to save inputs that only add new coverage bits (but no new responsibilities). */
    static final boolean SAVE_NEW_COUNTS = true;

    /** Whether to steal responsibility from old inputs (this increases computation cost). */
    static final boolean STEAL_RESPONSIBILITY = Boolean.getBoolean("jqf.ei.STEAL_RESPONSIBILITY");

    /** Probability of splicing in getOrGenerateFresh() */
    static final double DEMAND_DRIVEN_SPLICING_PROBABILITY = 0;

    static final int UNIQUE_SENSITIVITY = Integer.getInteger("jqf.ei.UNIQUE_SENSITIVITY", Integer.MAX_VALUE);

    static final boolean PROFILE_HEAP_USAGE = Boolean.valueOf(System.getenv("PROFILE_HEAP") != null ? System.getenv("PROFILE_HEAP") : "false");

    private MemoryMXBean memoryMXBean;

    /**
     * CONFETTI might ask that some specific bytes be mutated. This is how many times we'll try each place.
     */
    static final int MUTATIONS_PER_REQUESTED_MUTATION_LOCATION = 5;

    static final int MAX_HINTS_APPLIED_PER_INPUT_PER_FUZZING_CYCLE = 2000;

    private static ZestClient central;
    private ZestClient triggerClient;
    private RecordingInputStream ris;


    private long windowStartExecs = 0L;
    private double windowStartCoverage = 0.0;
    private double maxCoveragePercentageInWindow = 0.0;
    private Boolean startedCentral = false;
    private Boolean startCentral = false;

    private long campaignStartTime = System.currentTimeMillis();

    public static int extendedDictionarySize;

    /**
     * These two buffers are used by recordinginpustream, and could become quite large. We don't want to allocate them for each
     * input, and making them static in RecordingInputStream will cause a nasty thread safety bug one day, surely...
     */
    private final ByteArrayList  recordingInputStreamBuffer = new ByteArrayList(ZestGuidance.MAX_INPUT_SIZE / 4);
    private final IntArrayList recordingInputStreamMarksBuffer = new IntArrayList(ZestGuidance.MAX_INPUT_SIZE / 16);

    /**
     * @param testName the name of test to display on the status screen
     * Creates a new execution-index-parametric guidance.
     *
     * @param duration the amount of time to run fuzzing for, where
     *                 {@code null} indicates unlimited time.
     * @param outputDirectory the directory where fuzzing results will be written
     * @throws IOException if the output directory could not be prepared
     */
    public ZestGuidance(String testName, Duration duration,Integer heartbeatDuration, File outputDirectory) throws IOException {
        this.testName = testName;
        this.maxDurationMillis = duration != null ? duration.toMillis() : Long.MAX_VALUE;
        this.outputDirectory = outputDirectory;
        this.heartbeatInterval = heartbeatDuration;
        SingleSnoop.setCoverageListener(runCoverage);

        prepareOutputDirectory();

        // Try to parse the single-run timeout
        String timeout = System.getProperty("jqf.ei.TIMEOUT");
        if (timeout != null && !timeout.isEmpty()) {
            try {
                // Interpret the timeout as milliseconds (just like `afl-fuzz -t`)
                this.singleRunTimeoutMillis = Long.parseLong(timeout);
            } catch (NumberFormatException e1) {
                throw new IllegalArgumentException("Invalid timeout duration: " + timeout);
            }
        }

        String combinationsLimitProperty = System.getProperty("hintCombinations");
        if (combinationsLimitProperty != null) this.combinationsLimit = Integer.parseInt(combinationsLimitProperty);

        try {
            this.triggerClient = new ZestClient();
            if(this.triggerClient.triggerZ3SampleThreshold == null && this.triggerClient.triggerZ3SampleWindow == null) {
                this.central = triggerClient;
                startedCentral = true;
            }
        } catch (IOException e) {
            this.triggerClient = null;
        }
    }



    protected final synchronized void handleHeartbeat(long numExecs, double coveragePercentage) {
        if (this.central == null && this.triggerClient == null )
            return;

        if (!startedCentral && this.windowStartExecs == 0) {
            this.windowStartExecs = numExecs;
            this.windowStartCoverage = coveragePercentage;
            this.maxCoveragePercentageInWindow = coveragePercentage;
        }
        else if(this.windowStartExecs > 0 && (numExecs - this.windowStartExecs) < this.triggerClient.triggerZ3SampleWindow) {
            if(coveragePercentage > this.maxCoveragePercentageInWindow) {
                if( ((coveragePercentage - this.maxCoveragePercentageInWindow) / this.windowStartCoverage) * 100.0  > this.triggerClient.triggerZ3SampleThreshold){
                    this.windowStartExecs = numExecs;
                    this.windowStartCoverage = coveragePercentage;
                }
                this.maxCoveragePercentageInWindow = coveragePercentage;
            }
        } else if(this.windowStartExecs != 0 && (numExecs - this.windowStartExecs) >= this.triggerClient.triggerZ3SampleWindow) {
            if( ((maxCoveragePercentageInWindow - this.windowStartCoverage) / this.windowStartCoverage) * 100.0  < this.triggerClient.triggerZ3SampleThreshold) {
                //System.out.println("STARTING CENTRAL NOW!!!!!");
                this.startCentral = true;
                this.z3ThreadStartedInputNum = numExecs;
                windowStartExecs = 0L;
                maxCoveragePercentageInWindow = 0.0;
            } else {
                this.windowStartExecs = numExecs;
                this.windowStartCoverage = coveragePercentage;
                this.maxCoveragePercentageInWindow = coveragePercentage;
            }
        }

    }

    /**
     * @param testName the name of test to display on the status screen
     * @param duration the amount of time to run fuzzing for, where
     *                 {@code null} indicates unlimited time.
     * @param outputDirectory the directory where fuzzing results will be written
     * @param seedInputFiles one or more input files to be used as initial inputs
     * @throws IOException if the output directory could not be prepared
     */
    public ZestGuidance(String testName, Duration duration, Integer heartbeatDuration, File outputDirectory, File... seedInputFiles) throws IOException {
        this(testName, duration, heartbeatDuration, outputDirectory);
        if(seedInputFiles.length == 1 && seedInputFiles[0].isDirectory()){
            for(File f : seedInputFiles[0].listFiles()){
                if(f.getName().endsWith(".input")){
                    continue;
                }
                try {
                    seedInputs.add(new SeedInput(f));
                }catch(Throwable t){
                    System.err.println("Unable to read seed " + f);
                    t.printStackTrace();
                }
            }
        } else {
            for (File seedInputFile : seedInputFiles) {
                seedInputs.add(new SeedInput(seedInputFile));
            }
        }
    }

    private void prepareOutputDirectory() throws IOException {

        // Create the output directory if it does not exist
        if (!outputDirectory.exists()) {
            if (!outputDirectory.mkdirs()) {
                throw new IOException("Could not create output directory" +
                        outputDirectory.getAbsolutePath());
            }
        }

        // Make sure we can write to output directory
        if (!outputDirectory.isDirectory() || !outputDirectory.canWrite()) {
            throw new IOException("Output directory is not a writable directory: " +
                    outputDirectory.getAbsolutePath());
        }

        // Name files and directories after AFL
        this.savedInputsDirectory = new File(outputDirectory, "corpus");
        this.savedInputsDirectory.mkdirs();
        this.savedFailuresDirectory = new File(outputDirectory, "failures");
        this.savedFailuresDirectory.mkdirs();
        this.statsFile = new File(outputDirectory, "plot_data");
        this.logFile = new File(outputDirectory, "fuzz.log");
        this.currentInputFile = new File(outputDirectory, ".cur_input");


        // Delete everything that we may have created in a previous run.
        // Trying to stay away from recursive delete of parent output directory in case there was a
        // typo and that was not a directory we wanted to nuke.
        // We also do not check if the deletes are actually successful.
        statsFile.delete();
        logFile.delete();
        for (File file : savedInputsDirectory.listFiles()) {
            file.delete();
        }
        for (File file : savedFailuresDirectory.listFiles()) {
            file.delete();
        }

        statsWriter = new PrintWriter(new FileWriter(this.statsFile));
        if(PROFILE_HEAP_USAGE){
            memoryMXBean = ManagementFactory.getMemoryMXBean();
        }
        Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
            @Override
            public void run() {
                if(statsWriter != null){
                    statsWriter.flush();
                    statsWriter.close();
                }
            }
        }));

        appendToStatsFile("# unix_time, cycles_done, cur_path, paths_total, pending_total, " +
                "pending_favs, map_size, unique_crashes, unique_hangs, max_depth, execs_per_sec, total_inputs, " +
                "mutated_bytes, valid_inputs, invalid_inputs, all_cov, z3, " +
                "inputsSavedBy_StrHint, inputsCreatedBy_StrHint, inputsSavedBy_MultipleStrHint, inputsCreatedBy_MultipleStrHint, inputsSavedBy_CharHint, inputsCreatedBy_CharHint, " +
                "inputsSavedBy_Z3, inputsCreatedBy_Z3, " +
                "inputsSavedBy_Random, inputsCreatedBy_Random, " +
                "inputsSavedWith_Hints, " +
                "inputsSavedWith_Z3Origin, " +
                "inputsSavedWithoutHintsOrZ3,countOfSavedInputsWithExtendedDictionaryHints," +
                "countOfCreatedInputsWithExtendedDictionaryHints," +
                "extendedDictionarySize,heapUsageBytes,nonHeapUsageBytes");
    }

    static PrintWriter statsWriter;

    private static void appendToStatsFile(String line){
        statsWriter.println(line);
    }

    private static void appendLineToFile(File file, String line) throws GuidanceException {
        try (PrintWriter out = new PrintWriter(new FileWriter(file, true))) {
            out.println(line);
        } catch (IOException e) {
            throw new GuidanceException(e);
        }

    }

    private static void infoLog(String str, Object... args) {
        if (verbose) {
            String line = String.format(str, args);
            if (logFile != null) {
                appendLineToFile(logFile, line);

            } else {
                System.err.println(line);
            }
        }
    }

    private String millisToDuration(long millis) {
        long seconds = TimeUnit.MILLISECONDS.toSeconds(millis % TimeUnit.MINUTES.toMillis(1));
        long minutes = TimeUnit.MILLISECONDS.toMinutes(millis % TimeUnit.HOURS.toMillis(1));
        long hours = TimeUnit.MILLISECONDS.toHours(millis);
        String result = "";
        if (hours > 0) {
            result = hours + "h ";
        }
        if (hours > 0 || minutes > 0) {
            result += minutes + "m ";
        }
        result += seconds + "s";
        return result;
    }

    // Call only if console exists
    private void displayStats() {

        Date now = new Date();
        long intervalMilliseconds = now.getTime() - lastRefreshTime.getTime();
        if (intervalMilliseconds < STATS_REFRESH_TIME_PERIOD) {
            return;
        }
        long interlvalTrials = numTrials - lastNumTrials;
        long intervalExecsPerSec = interlvalTrials * 1000L / intervalMilliseconds;
        double intervalExecsPerSecDouble = interlvalTrials * 1000.0 / intervalMilliseconds;
        lastRefreshTime = now;
        lastNumTrials = numTrials;
        long elapsedMilliseconds = now.getTime() - startTime.getTime();
        long execsPerSec = numTrials * 1000L / elapsedMilliseconds;

        String currentParentInputDesc;
        if (seedInputs.size() > 0 || savedInputs.isEmpty()) {
            currentParentInputDesc = "<seed>";
        } else {
            Input currentParentInput = savedInputs.get(currentParentInputIdx);
            currentParentInputDesc = currentParentInputIdx + " ";
            currentParentInputDesc += currentParentInput.isFavored() ? "(favored)" : "(not favored)";
            currentParentInputDesc += " {" + numChildrenGeneratedForCurrentParentInput +
                    "/" + getTargetChildrenForParent(currentParentInput) + " mutations, including " + currentParentInput.bonusMutations + "/" + currentParentInput.hintsRemaining + " hints}";
        }

        int nonZeroCount = totalCoverage.getNonZeroCount();
        double nonZeroFraction = nonZeroCount * 100.0 / totalCoverage.size();
        int nonZeroValidCount = validCoverage.getNonZeroCount();
        double nonZeroValidFraction = nonZeroValidCount * 100.0 / validCoverage.size();
        if(!QUIET_MODE && console != null){
            console.printf("\033[2J");
            console.printf("\033[H");
            console.printf("Zest: Validity Fuzzing with Parametric Generators\n");
            console.printf("-------------------------------------------------\n");
            if (this.testName != null) {
                console.printf("Test name:            %s\n", this.testName);
            }
            console.printf("Results directory:    %s\n", this.outputDirectory.getAbsolutePath());
            if (SHOW_CONFIG) {
                if (TOTALLY_RANDOM) {
                    console.printf("Config:               TOTALLY_RANDOM\n");
                } else {
                    console.printf("Config:               DISABLE_EXECUTION_INDEXING = %s,\n" +
                                    "                      STEAL_RESPONSIBILITY       = %s,\n" +
                                    "                      SPLICE_SUBTREE             = %s\n\n",
                            DISABLE_EXECUTION_INDEXING, STEAL_RESPONSIBILITY, SPLICE_SUBTREE);
                }
            }
            console.printf("Elapsed time:         %s (%s)\n", millisToDuration(elapsedMilliseconds),
                    maxDurationMillis == Long.MAX_VALUE ? "no time limit" : ("max " + millisToDuration(maxDurationMillis)));
            console.printf("Number of executions: %,d\n", numTrials);
            console.printf("Valid inputs:         %,d (%.2f%%)\n", numValid, numValid * 100.0 / numTrials);
            console.printf("Cycles completed:     %d\n", cyclesCompleted);
            console.printf("Unique failures:      %,d\n", uniqueFailures.size());
            console.printf("Queue size:           %,d (%,d favored last cycle)\n", savedInputs.size(), numFavoredLastCycle);
            console.printf("Current parent input: %s\n", currentParentInputDesc);
            console.printf("Execution speed:      %,d/sec now | %,d/sec overall\n", intervalExecsPerSec, execsPerSec);
            if(PROFILE_HEAP_USAGE){
                console.printf("Heap memory used:     %,d MB\n", memoryMXBean.getHeapMemoryUsage().getUsed()/(1024*1024));
                console.printf("Non-heap memory used: %,d MB\n", memoryMXBean.getNonHeapMemoryUsage().getUsed()/(1024*1024));
            }
            console.printf("Total coverage:       %,d (%.2f%% of map)\n", nonZeroCount, nonZeroFraction);
            console.printf("Valid coverage:       %,d (%.2f%% of map)\n", nonZeroValidCount, nonZeroValidFraction);
            console.printf("Extended dict size:   %,d\n", extendedDictionarySize);
            console.printf("Coverage-revealing inputs generated by:\n");
            console.printf("    A string hint:        %,d/%,d\n", countOfInputsSavedByMutation[MutationType.APPLY_SINGLE_HINT.ordinal()],
                    countOfInputsCreatedByMutation[MutationType.APPLY_SINGLE_HINT.ordinal()]);
            console.printf("    Multiple hints:       %,d/%,d\n", countOfInputsSavedByMutation[MutationType.APPLY_MULTIPLE_HINTS.ordinal()],
                    countOfInputsCreatedByMutation[MutationType.APPLY_MULTIPLE_HINTS.ordinal()]);
            console.printf("    A char hint:          %,d/%,d\n", countOfInputsSavedByMutation[MutationType.APPLY_SINGLE_CHAR_HINT.ordinal()],
                    countOfInputsCreatedByMutation[MutationType.APPLY_SINGLE_CHAR_HINT.ordinal()]);
            console.printf("    An Z3 hint:           %,d/%,d\n", countOfInputsSavedByMutation[MutationType.APPLY_Z3_HINT.ordinal()],
                    countOfInputsCreatedByMutation[MutationType.APPLY_Z3_HINT.ordinal()]);
            console.printf("    An Z3 hint, extended: %,d/%,d\n", countOfInputsSavedByMutation[MutationType.APPLY_Z3_HINT_EXTENDED.ordinal()],
                    countOfInputsCreatedByMutation[MutationType.APPLY_Z3_HINT_EXTENDED.ordinal()]);
            //console.printf("    Mutating before hints:%,d/%,d\n", countOfInputsSavedByMutation[MutationType.BEFORE_HINTS.ordinal()],
            //countOfInputsCreatedByMutation[MutationType.BEFORE_HINTS.ordinal()]);
            //console.printf("    Mutating after hints: %,d/%,d\n", countOfInputsSavedByMutation[MutationType.AFTER_HINTS.ordinal()],
            //countOfInputsCreatedByMutation[MutationType.AFTER_HINTS.ordinal()]);
            //console.printf("    Mutating near hints:  %,d/%,d\n", countOfInputsSavedByMutation[MutationType.AFTER_HINTS_BUT_NEAR.ordinal()],
            //        countOfInputsCreatedByMutation[MutationType.AFTER_HINTS_BUT_NEAR.ordinal()]);
            console.printf("    Mutating randomly:    %,d/%,d\n", countOfInputsSavedByMutation[MutationType.RANDOM.ordinal()],
                    countOfInputsCreatedByMutation[MutationType.RANDOM.ordinal()]);
            console.printf("     (Extended dictionary)%,d/%,d\n", countOfSavedInputsWithExtendedDictionaryHints, countOfCreatedInputsWithExtendedDictionaryHints);
            console.printf("    Mutating targeted:    %,d/%,d\n", countOfInputsSavedByMutation[MutationType.TARGETED_RANDOM.ordinal()],
                    countOfInputsCreatedByMutation[MutationType.TARGETED_RANDOM.ordinal()]);
            console.printf("Inputs saved by mutation count:\n");
            console.printf("    0:                %,d/%,d\n", countOfInputsSavedWithMutationCounts[0], countOfInputsCreatedWithMutationCounts[0]);
            console.printf("    1:                %,d/%,d\n", countOfInputsSavedWithMutationCounts[1], countOfInputsCreatedWithMutationCounts[1]);
            console.printf("    1-5:              %,d/%,d\n", countOfInputsSavedWithMutationCounts[2], countOfInputsCreatedWithMutationCounts[2]);
            console.printf("    5-10:             %,d/%,d\n", countOfInputsSavedWithMutationCounts[3], countOfInputsCreatedWithMutationCounts[3]);
            console.printf("    10-20:            %,d/%,d\n", countOfInputsSavedWithMutationCounts[4], countOfInputsCreatedWithMutationCounts[4]);
            console.printf("    20-100:           %,d/%,d\n", countOfInputsSavedWithMutationCounts[5], countOfInputsCreatedWithMutationCounts[5]);
            console.printf("    100-1,000:        %,d/%,d\n", countOfInputsSavedWithMutationCounts[6], countOfInputsCreatedWithMutationCounts[6]);
            console.printf("    1,000-10,000:     %,d/%,d\n", countOfInputsSavedWithMutationCounts[7], countOfInputsCreatedWithMutationCounts[7]);
            console.printf("Inputs saved by HINT mutation count:\n");
            console.printf("    0:                %,d/%,d\n", countOfInputsSavedWithHintMutationCounts[0], countOfInputsCreatedWithHintMutationCounts[0]);
            console.printf("    1:                %,d/%,d\n", countOfInputsSavedWithHintMutationCounts[1], countOfInputsCreatedWithHintMutationCounts[1]);
            console.printf("    1-5:              %,d/%,d\n", countOfInputsSavedWithHintMutationCounts[2], countOfInputsCreatedWithHintMutationCounts[2]);
            console.printf("    5-10:             %,d/%,d\n", countOfInputsSavedWithHintMutationCounts[3], countOfInputsCreatedWithHintMutationCounts[3]);
            console.printf("    10-20:            %,d/%,d\n", countOfInputsSavedWithHintMutationCounts[4], countOfInputsCreatedWithHintMutationCounts[4]);
            console.printf("    20-100:           %,d/%,d\n", countOfInputsSavedWithHintMutationCounts[5], countOfInputsCreatedWithHintMutationCounts[5]);
            console.printf("    100-1,000:        %,d/%,d\n", countOfInputsSavedWithHintMutationCounts[6], countOfInputsCreatedWithHintMutationCounts[6]);
            console.printf("    1,000-10,000:     %,d/%,d\n", countOfInputsSavedWithHintMutationCounts[7], countOfInputsCreatedWithHintMutationCounts[7]);

            console.printf("Saved inputs derived from:\n");
            console.printf("    Hints             %,d\n", countOfSavedInputsBySeedSource[SeedSource.HINTS.ordinal()]);
            console.printf("    Z3                %,d\n", countOfSavedInputsBySeedSource[SeedSource.Z3.ordinal()]);
            console.printf("    Other             %,d\n", countOfSavedInputsBySeedSource[SeedSource.RANDOM.ordinal()]);
            console.printf("Failure inducing inputs derived from:\n");
            console.printf("    Hints             %,d\n", countOfFailingInputsBySeedSource[SeedSource.HINTS.ordinal()]);
            console.printf("    Z3                %,d\n", countOfFailingInputsBySeedSource[SeedSource.Z3.ordinal()]);
            console.printf("    Other             %,d\n", countOfFailingInputsBySeedSource[SeedSource.RANDOM.ordinal()]);
        }
        long numinputsSavedWithoutHints =  savedInputs.size() - countOfInputsSavedByMutation[MutationType.APPLY_Z3_HINT.ordinal()]
                - countOfInputsSavedByMutation[MutationType.APPLY_SINGLE_HINT.ordinal()]
                - countOfInputsSavedByMutation[MutationType.APPLY_SINGLE_CHAR_HINT.ordinal()];
        long numInputsCreatedWithoutHints = numTrials - countOfInputsCreatedByMutation[MutationType.APPLY_Z3_HINT.ordinal()]
                - countOfInputsCreatedByMutation[MutationType.APPLY_SINGLE_HINT.ordinal()]
                - countOfInputsCreatedByMutation[MutationType.APPLY_SINGLE_CHAR_HINT.ordinal()];

        String plotData = String.format("%d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %.2f, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d",
                TimeUnit.MILLISECONDS.toSeconds(now.getTime()), cyclesCompleted, currentParentInputIdx,
                savedInputs.size(), 0, 0, nonZeroCount, uniqueFailures.size(), 0, 0, intervalExecsPerSecDouble,
                numTrials, mutatedBytes/numTrials, numValid, numTrials-numValid, nonZeroCount,
                (z3ThreadStartedInputNum != -1) && (numTrials >= z3ThreadStartedInputNum) ? 1: 0,
                countOfInputsSavedByMutation[MutationType.APPLY_SINGLE_HINT.ordinal()],
                countOfInputsCreatedByMutation[MutationType.APPLY_SINGLE_HINT.ordinal()],

                countOfInputsSavedByMutation[MutationType.APPLY_MULTIPLE_HINTS.ordinal()],
                countOfInputsCreatedByMutation[MutationType.APPLY_MULTIPLE_HINTS.ordinal()],

                countOfInputsSavedByMutation[MutationType.APPLY_SINGLE_CHAR_HINT.ordinal()],
                countOfInputsCreatedByMutation[MutationType.APPLY_SINGLE_CHAR_HINT.ordinal()],
                countOfInputsSavedByMutation[MutationType.APPLY_Z3_HINT.ordinal()],
                countOfInputsCreatedByMutation[MutationType.APPLY_Z3_HINT.ordinal()],
                numinputsSavedWithoutHints,numInputsCreatedWithoutHints,
                countOfSavedInputsBySeedSource[SeedSource.HINTS.ordinal()],
                countOfSavedInputsBySeedSource[SeedSource.Z3.ordinal()],
                countOfSavedInputsBySeedSource[SeedSource.RANDOM.ordinal()],
                countOfSavedInputsWithExtendedDictionaryHints,
                countOfCreatedInputsWithExtendedDictionaryHints,
                ZestGuidance.extendedDictionarySize);
        if(PROFILE_HEAP_USAGE){
            plotData += ", " + memoryMXBean.getHeapMemoryUsage().getUsed() + ", " + memoryMXBean.getNonHeapMemoryUsage().getUsed();
        }
        appendToStatsFile(plotData);

    }

    private int getTargetChildrenForParent(Input parentInput) {
        // Baseline is a constant
        int target = NUM_CHILDREN_BASELINE;


        // We like inputs that cover many things, so scale with fraction of max
        if (maxCoverage > 0) {
            target = (NUM_CHILDREN_BASELINE * parentInput.nonZeroCoverage) / maxCoverage;
        }

        // We absolutey love favored inputs, so fuzz them more
        if (parentInput.isFavored()) {
            target = target * NUM_CHILDREN_MULTIPLIER_FAVORED;
        }

        target += parentInput.bonusMutations;
        return target;
    }

    private void completeCycle() {
        // Increment cycle count
        cyclesCompleted++;
        infoLog("\n# Cycle " + cyclesCompleted + " completed.");
        if(!FETCH_HINTS_MID_CYCLE){
            //Find inputs that we now have hints for
            if(central != null){
                LinkedList<Integer> fetchHintsFor = central.getRecommendations();
                for(Integer i : fetchHintsFor){
                    this.inputsWithHintsAtStartOfCycle.add(i.intValue());
                }
            }
        }

        // Go over all inputs and do a sanity check (plus log)
        infoLog("Here is a list of favored inputs:");
        int sumResponsibilities = 0;
        numFavoredLastCycle = 0;
        for (Input input : savedInputs) {

            // refill the priority queue
            if(priorityQueueConfig.usePriorityQueue) {
                savedInputsAccess.add(input);
            }

            if (input.isFavored()) {
                int responsibleFor = input.responsibilities.size();
                infoLog("Input %d is responsible for %d branches", input.id, responsibleFor);
                sumResponsibilities += responsibleFor;
                numFavoredLastCycle++;
            }
        }

        int totalCoverageCount = totalCoverage.getNonZeroCount();
        infoLog("Total %d branches covered", totalCoverageCount);
        if (sumResponsibilities != totalCoverageCount) {
            //throw new AssertionError("Responsibilty mistmatch: " + sumResponsibilities + " vs " + totalCoverageCount);
            System.err.println("Responsibility mismatch: " + sumResponsibilities + " vs " + totalCoverageCount);
        }

        // Refresh ecToInputLoc so that subsequent splices are only from favored inputs
        ecToInputLoc.clear();
        for (Input input : savedInputs) {
            if (input.isFavored()) {
                mapEcToInputLoc(input);
            }
        }

        // Break log after cycle
        infoLog("\n\n\n");
    }

    @Override
    public InputStream getInput() throws GuidanceException {


        // Clear coverage stats for this run
        runCoverage.clear();

        // Reset execution index state
        eiState = new ExecutionIndexingState();

        Coordinator.Input inputFromCentral;

        // Choose an input to execute based on state of queues
        if (!seedInputs.isEmpty()) {
            // First, if we have some specific seeds, use those
            currentInput = seedInputs.removeFirst();

            // Hopefully, the seeds will lead to new coverage and be added to saved inputs

        } else if (savedInputs.isEmpty()) {
            // If no seeds given try to start with something random
            if (!TOTALLY_RANDOM && numTrials > 100_000) {
                throw new GuidanceException("Too many trials without coverage; " +
                        "likely all assumption violations");
            }

            // Make fresh input using either list or maps
            infoLog("Spawning new input from thin air");
            currentInput = DISABLE_EXECUTION_INDEXING ? new LinearInput() : new MappedInput();
            currentInput.seedSource = SeedSource.RANDOM;

        } else{
            // The number of children to produce is determined by how much of the coverage
            // pool this parent input hits
            Input currentParentInput = savedInputs.get(currentParentInputIdx);
            int targetNumChildren = getTargetChildrenForParent(currentParentInput);
            if (numChildrenGeneratedForCurrentParentInput >= targetNumChildren &&
                    central != null && (inputFromCentral = central.getInput()) != null) {
                // Central sent input, use that instead

                currentInput = new ZestGuidance.SeedInput(inputFromCentral.bytes, "From central");
                currentInput.seedSource = SeedSource.Z3;
                currentInput.z3 = true; // the only inputs we get from the central this way are z3
                if(!inputFromCentral.hintGroups.isEmpty()){
                    if(inputFromCentral.hintGroups.size() > 1){
                        System.err.println("Unexpected... shouldn't there be only one hint group per Z3 input for now?");
                    }
                    currentInput.mutationType = MutationType.APPLY_Z3_HINT;
                    Coordinator.StringHintGroup hints = inputFromCentral.hintGroups.getFirst();
                    currentInput.stringEqualsHints = new LinkedList<>();
                    currentInput.instructions = hints.instructions;
                    for(Coordinator.StringHint h : hints.hints){
                        currentInput.stringEqualsHints.add(new Coordinator.StringHint[]{h});
                    }
                    //Heuristic: We might be getting strings out of Z3 that are too short ot process. Try also running the same input with longer strings
                    Coordinator.StringHintGroup doubled = new Coordinator.StringHintGroup();
                    for(int i = 0; i < hints.instructions.size(); i++){
                        doubled.instructions.add(hints.instructions.get(i));
                        Coordinator.StringHint h = hints.hints.get(i);
                        doubled.hints.add(new Coordinator.StringHint(h.getHint()+"a", h.getType(), null));
                    }
                    currentInput.bonusMutations++;
                    currentInput.stringHintGroupsToTryInChildren.add(doubled);
                }

                // Write it to disk for debugging
                //try {
                //    writeCurrentInputToFile(currentInputFile);
                //} catch (IOException ignore) {
                //}

                // Start time-counting for timeout handling
                this.runStart = new Date();
                this.branchCount = 0;
            } else {
                boolean newParent = false;
                boolean getRecommendations = false;

                if (numChildrenGeneratedForCurrentParentInput >= targetNumChildren) {
                    // Select the next saved input to fuzz
                    if (FETCH_HINTS_MID_CYCLE && recommendedInputsToFuzz.isEmpty() && central != null && triggerClient != null) {
                        recommendedInputsToFuzz = triggerClient.getRecommendations();
                    }
                    if (FETCH_HINTS_MID_CYCLE && !recommendedInputsToFuzz.isEmpty()) {
                        if (recommendedInputsToFuzz.peek() > currentParentInputCounter + 1) {
                            currentParentInputCounter++;
                            currentParentInputIdx = currentParentInputCounter;
                        } else {
                            currentParentInputIdx = recommendedInputsToFuzz.pop();
                            if(currentParentInputIdx == currentParentInputCounter + 1){
                                currentParentInputCounter++;
                            }
                            getRecommendations = true;
                        }
                    }
                    else if (priorityQueueConfig.usePriorityQueue)
                        currentParentInputIdx = savedInputsAccess.remove().id;
                    else {
                        currentParentInputCounter = (currentParentInputCounter + 1) % savedInputs.size();
                        currentParentInputIdx = currentParentInputCounter;
                    }
                    if(!FETCH_HINTS_MID_CYCLE && inputsWithHintsAtStartOfCycle.contains(currentParentInputIdx)){
                        getRecommendations = true;
                        inputsWithHintsAtStartOfCycle.remove(currentParentInputIdx);
                    }

                    // Count cycles
                    // if (currentParentInputIdx == 0) {
                    if ((priorityQueueConfig.usePriorityQueue  && savedInputsAccess.isEmpty()) || (!priorityQueueConfig.usePriorityQueue && currentParentInputIdx == 0)) {
                        completeCycle(); //TODO should probably revisit priority queue...
                    }

                    numChildrenGeneratedForCurrentParentInput = 0;
                    numChildrenGeneratedForCurrentMutationLocation = 0;
                    newParent = true;
                }
                Input parent = savedInputs.get(currentParentInputIdx);
                parent.lastFuzzedCycle = cyclesCompleted;

                if(newParent){
                    parent.numHintsAppliedThisRound = 0;
                }

                if (newParent && getRecommendations && central != null) {
                    try {
                        central.selectInput(parent.id);
                        LinkedList<int[]> instructionsToTryInChildren = central.receiveInstructions();
                        LinkedList<Coordinator.StringHint[]> stringEqualsHintsToTryInChildren = central.receiveStringEqualsHints();
                        HashSet<Coordinator.TargetedHint> targetedHints = central.receiveTargetedHints();
                        if (!parent.alreadyReceivedHints) {
                            //Not sure why this happens, but also not sure if it's a big deal?
                            //if(instructionsToTryInChildren.isEmpty()){
                                //throw new IllegalStateException("Central didn't send instructions for input "+ parent.id + " even though it suggested it!");
                            //}
                            parent.alreadyReceivedHints = true;
                            parent.instructionsToTryInChildren = instructionsToTryInChildren;
                            parent.stringEqualsHintsToTryInChildren = stringEqualsHintsToTryInChildren;
                            parent.targetedHintsToTryInChildren = new LinkedList(targetedHints);
                            for(Coordinator.TargetedHint h : targetedHints){
                                h.apply(parent);
                            }

                            parent.allInstructions = new LinkedList(parent.instructionsToTryInChildren);
                            parent.allStringEqualsHints = new LinkedList();
                            for(Object each : parent.stringEqualsHintsToTryInChildren){
                                Coordinator.StringHint[] sh = (Coordinator.StringHint[]) each;
                                parent.allStringEqualsHints.add(sh.clone());
                            }
                            //parent.addExtraRandomStringEqualsHints(random);
                            parent.bonusMutations = 0;
                            parent.updateHintsRemainingCount();
                            parent.organizeStringHintsForCombinations();
                            if(INCLUDE_SINGLE_HINTS_AS_BONUS_MUTATIONS)
                                parent.bonusMutations = Math.min(parent.hintsRemaining, getTargetChildrenForParent(parent));
                            //Save the input again, since we now have hints for it!
                            writeInputToFile(parent, new File(savedInputsDirectory, String.format("id_%06d", parent.id)));

                        }

                    } catch (IOException e) {
                        throw new Error(e);
                    }
                }
                if(newParent && !getRecommendations && parent.bonusMutations > 0){
                    //Make sure that the number of bonus mutations falls as we run out of hints.
                    // CONFETTI will always get to generate its own set of children inputs
                    parent.updateHintsRemainingCount();
                    if(INCLUDE_SINGLE_HINTS_AS_BONUS_MUTATIONS)
                        parent.bonusMutations = Math.min(parent.hintsRemaining, getTargetChildrenForParent(parent));
                }

                // Fuzz it to get a new input
                infoLog("Mutating input: %s", parent.desc);
                currentInput = parent.fuzz(random);
                currentInput.parentInputIdx = currentParentInputIdx;
                numChildrenGeneratedForCurrentParentInput++;

                // Write it to disk for debugging
                //try {
                //    writeCurrentInputToFile(currentInputFile);
                //} catch (IOException ignore) { }

                // Start time-counting for timeout handling
                this.runStart = new Date();
                this.branchCount = 0;
            }
        }

        if(currentInput.mutationType != null)
            this.countOfInputsCreatedByMutation[currentInput.mutationType.ordinal()]++;

        // Return an input stream that uses the EI map
        InputStream is = new InputStream() {
            int bytesRead = 0;

            @Override
            public int read() throws IOException {

                // lastEvent must not be null
                if (DISABLE_EXECUTION_INDEXING == false && lastEvent == null) {
                    throw new IOException("Could not compute execution index; no instrumentation?");
                }

                // For linear inputs, get with key = bytesRead (which is then incremented)
                if (currentInput instanceof LinearInput) {
                    LinearInput linearInput = (LinearInput) currentInput;
                    // Attempt to get a value from the list, or else generate a random value
                    int ret = linearInput.getOrGenerateFresh(bytesRead++, random);
                    // infoLog("read(%d) = %d", bytesRead, ret);
                    return ret;
                }

                // For mapped inputs, make a suitable execution index
                else {
                    MappedInput mappedInput = (MappedInput) currentInput;

                    // Get the execution index of the last event
                    ExecutionIndex executionIndex = eiState.getExecutionIndex(lastEvent);

                    // Attempt to get a value from the map, or else generate a random value
                    int value = mappedInput.getOrGenerateFresh(executionIndex, random);

                    // Keep track of how many bytes were read in this input
                    bytesRead++;

                    return value;

                }
            }
        };

        if (central != null || triggerClient != null) {
            ris = new RecordingInputStream(is, recordingInputStreamBuffer, recordingInputStreamMarksBuffer);
            is = ris;

            if ((currentInput.stringEqualsHints != null))
                is = new StringEqualsHintingInputStream(is, ris, currentInput);
        }

        return is;
    }

    @Override
    public boolean hasInput() {
        Date now = new Date();
        long elapsedMilliseconds = now.getTime() - startTime.getTime();
        return elapsedMilliseconds < maxDurationMillis;
    }

    private Object[] args;

    @Override
    public void setArgs(Object[] args) {
        this.args = args;
    }

    @Override
    public void handleResult(Result result, Throwable error) throws GuidanceException {

        if(currentInput.numGlobalDictionaryHintsApplied > 0) {
            this.countOfCreatedInputsWithExtendedDictionaryHints++;
            if(currentInput.seedSource == SeedSource.RANDOM)
                currentInput.seedSource = SeedSource.HINTS;
        }

        if(!this.startedCentral && this.startCentral) {
            throw new UnsupportedOperationException("Trigger client code is removed, this shouldn't happen...");
        }


        // Stop timeout handling
        this.runStart = null;


        // stop collecting coverage for the run
        runCoverage.lock();

        // Increment run count
        this.numTrials++;

        // Trim input (remove unused keys)
        currentInput.gc();

        // It must still be non-empty
        assert(currentInput.size() > 0) : String.format("Empty input: %s", currentInput.desc);

        boolean valid = result == Result.SUCCESS;

        // send a
        if( !startedCentral &&  ((numTrials > 0 )&& (numTrials % heartbeatInterval ) == 0)) {
            double coveragePercentage = totalCoverage.getNonZeroCount() * 100.0 / totalCoverage.size();
            handleHeartbeat(numTrials, coveragePercentage);

        }

//        // jacoco coverage
//        try {
//            // Get exec data by dynamically calling RT.getAgent().getExecutionData()
//            Class RT = Class.forName("org.jacoco.agent.rt.RT");
//            Method getAgent = RT.getMethod("getAgent");
//            Object agent = getAgent.invoke(null);
//            Method dump = agent.getClass().getMethod("getExecutionData", boolean.class);
//            byte[] execData = (byte[]) dump.invoke(agent, false);
//        }
//        catch (Exception e) {
//                //System.err.println(e);
//        }


        if (valid) {
            // Increment valid counter
            numValid++;
        }

        // New for us: save failing inputs too... why not!?
        if (result == Result.SUCCESS || result == Result.INVALID || result == Result.FAILURE) {

            // Coverage before
            int nonZeroBefore = totalCoverage.getNonZeroCount();
            int validNonZeroBefore = validCoverage.getNonZeroCount();

            // Compute a list of keys for which this input can assume responsiblity.
            // Newly covered branches are always included.
            // Existing branches *may* be included, depending on the heuristics used.
            // A valid input will steal responsibility from invalid inputs
            IntHashSet responsibilities = computeResponsibilities(valid);

            // Update total coverage
            boolean coverageBitsUpdated = totalCoverage.updateBits(runCoverage);
            if (valid) {
                validCoverage.updateBits(runCoverage);
            }

            // Coverage after
            int nonZeroAfter = totalCoverage.getNonZeroCount();
            if (nonZeroAfter > maxCoverage) {
                maxCoverage = nonZeroAfter;
            }
            int validNonZeroAfter = validCoverage.getNonZeroCount();

            // Possibly save input
            boolean toSave = false;
            String why = "";



            if(StringEqualsHintingInputStream.hintUsedInCurrentInput) {
               // StringEqualsHintingInputStream.hintUsedInCurrentInput = false;
                if(StringEqualsHintingInputStream.z3HintsUsedInCurrentInput) {
                    why= why + "+z3hint";
                    // always save z3 inputs
                    //toSave = true;
                    StringEqualsHintingInputStream.z3HintsUsedInCurrentInput = false;
                }
                else
                    why= why + "+hint";

               // toSave = true;
            }
            if (SAVE_NEW_COUNTS && coverageBitsUpdated) {
                toSave = true;
                why = why + "+count";
            }

            // Save if new total coverage found
            if (nonZeroAfter > nonZeroBefore) {
                // Must be responsible for some branch
                toSave = true;
                why = why + "+cov";
            }

            if (validNonZeroAfter > validNonZeroBefore) {
                // Must be responsible for some branch
                currentInput.valid = true;
                toSave = true;
                why = why + "+valid";
            }
            if(!toSave && currentInput.desc.contains("hint")){
                infoLog("No new coverage for %s", currentInput.desc);
            }

            if (toSave) {
                if(currentInput.mutationType != null){
                    this.countOfInputsSavedByMutation[((LinearInput) currentInput).mutationType.ordinal()]++;
                    int n = ((LinearInput) currentInput).numMutations;
                    for (int i = 0; i < this.countOfInputsSavedWithMutationCountsRanges.length; i++) {
                        if (n <= this.countOfInputsSavedWithMutationCountsRanges[i]) {
                            if (currentInput.mutationType == MutationType.APPLY_MULTIPLE_HINTS
                                    || currentInput.mutationType == MutationType.APPLY_SINGLE_HINT) {
                                this.countOfInputsSavedWithHintMutationCounts[i]++;
                            } else if (currentInput.mutationType == MutationType.RANDOM
                                //|| currentInput.mutationType == MutationType.AFTER_HINTS_BUT_NEAR
                                //|| currentInput.mutationType == MutationType.AFTER_HINTS
                                //|| currentInput.mutationType == MutationType.BEFORE_HINTS
                            ) {
                                this.countOfInputsSavedWithMutationCounts[i]++;
                            }
                            break;
                        }
                    }
                }
                if(currentInput.seedSource != null)
                    countOfSavedInputsBySeedSource[currentInput.seedSource.ordinal()]++;
                if(currentInput.numGlobalDictionaryHintsApplied > 0)
                    countOfSavedInputsWithExtendedDictionaryHints++;

                infoLog("Saving new input (at run %d): " +
                                "input #%d " +
                                "of size %d; " +
                                "total coverage = %d",
                        numTrials,
                        savedInputs.size(),
                        currentInput.size(),
                        nonZeroAfter);

                // Save input to queue and to disk
                try {
                    saveCurrentInput(responsibilities, why);
                } catch (IOException e) {
                    throw new GuidanceException(e);
                }

                if(central != null) {

                    try {
                        // Send new input / random requests used
                        Boolean hintsUsed = StringEqualsHintingInputStream.hintUsedInCurrentInput;

                        double coveragePercentage = totalCoverage.getNonZeroCount() * 100.0 / totalCoverage.size();
                        //if (!(currentInput instanceof SeedInput)) {
                            //Don't send seed inputs to central, they should already have hints
                            central.sendInput(ris.getRecordedInput(), result, currentInput,
                                    coveragePercentage, numTrials);

                            // Send updated coverage
                            central.sendCoverage(totalCoverage);
                        //}
                        StringEqualsHintingInputStream.hintUsedInCurrentInput = false;
                    } catch (IOException e) {
                        throw new Error(e);
                    }
                }

            }
        }
        if (result == Result.FAILURE || result == Result.TIMEOUT) {
            String msg = error.getMessage();

            if(currentInput.seedSource != null)
                countOfFailingInputsBySeedSource[currentInput.seedSource.ordinal()]++;

            // Get the root cause of the failure
            Throwable rootCause = error;
            while (rootCause.getCause() != null) {
                rootCause = rootCause.getCause();
            }

            // Attempt to add this to the set of unique failures
            StackTraceElement[] root = rootCause.getStackTrace();
            StackTraceElement[] trace;

            if (root.length < UNIQUE_SENSITIVITY) {
                trace = root;
            } else {
                trace = new StackTraceElement[Math.min(UNIQUE_SENSITIVITY, root.length)];
                System.arraycopy(root, 0, trace, 0, trace.length);
            }

            if (uniqueFailures.add(Arrays.asList(trace))) {

                // Save crash to disk
                try {
                    int crashIdx = uniqueFailures.size()-1;
                    String saveFileName = String.format("id_%06d", crashIdx);
                    File saveFile = new File(savedFailuresDirectory, saveFileName);
                    writeCurrentInputToFile(saveFile);
                    File traceFile = new File(savedFailuresDirectory, saveFileName + ".trace");
                    try (PrintWriter pw = new PrintWriter(new FileWriter(traceFile))) {
                        error.printStackTrace(pw);
                    }
                    File argsFile = new File(savedFailuresDirectory, saveFileName + ".input");
                    for (Object o : args)
                        saveInputToDisk(argsFile, o);
                    infoLog("%s","Found crash: " + error.getClass() + " - " + (msg != null ? msg : ""));
                    String how = currentInput.desc;
                    String why = result == Result.FAILURE ? "+crash" : "+hang";
                    infoLog("Saved - %s %s %s", saveFile.getPath(), how, why);
                } catch (IOException e) {
                    throw new GuidanceException(e);
                }

            }
        }

        displayStats();

        runCoverage.unlock();

    }


    // Compute a set of branches for which the current input may assume responsibility
    private IntHashSet computeResponsibilities(boolean valid) {
        IntHashSet result = new IntHashSet();

        // This input is responsible for all new coverage
        IntList newCoverage = runCoverage.computeNewCoverage(totalCoverage);
        if (newCoverage.size() > 0) {
            result.addAll(newCoverage);
        }

        // If valid, this input is responsible for all new valid coverage
        if (valid) {
            IntList newValidCoverage = runCoverage.computeNewCoverage(validCoverage);
            if (newValidCoverage.size() > 0) {
                result.addAll(newValidCoverage);
            }
        }

        // Perhaps it can also steal responsibility from other inputs
        if (STEAL_RESPONSIBILITY) {
            int currentNonZeroCoverage = runCoverage.getNonZeroCount();
            int currentInputSize = currentInput.size();
            IntHashSet covered = new IntHashSet();
            IntSinglyLinkedList.IntListIterator coveredIter = runCoverage.getCovered().iterator();
            while(coveredIter.hasNext()){
                int v = coveredIter.nextInt();
                covered.add(v);
            }

            // Search for a candidate to steal responsibility from
            candidate_search:
            for (Input candidate : savedInputs) {
                IntHashSet responsibilities = candidate.responsibilities;

                // Candidates with no responsibility are not interestig
                if (responsibilities.isEmpty()) {
                    continue candidate_search;
                }

                // To avoid thrashing, only consider candidates with either
                // (1) strictly smaller total coverage or
                // (2) same total coverage but strictly larger size
                if (candidate.nonZeroCoverage < currentNonZeroCoverage ||
                        (candidate.nonZeroCoverage == currentNonZeroCoverage &&
                                currentInputSize < candidate.size())) {

                    // Check if we can steal all responsibilities from candidate
                    IntIterator iter = responsibilities.intIterator();
                    while(iter.hasNext()){
                        int b = iter.next();
                        if (covered.contains(b) == false) {
                            // Cannot steal if this input does not cover something
                            // that the candidate is responsible for
                            continue candidate_search;
                        }
                    }
                    // If all of candidate's responsibilities are covered by the
                    // current input, then it can completely subsume the candidate
                    result.addAll(responsibilities);
                }

            }
        }

        return result;
    }

    private void writeCurrentInputToFile(File saveFile) throws IOException {
        writeInputToFile(currentInput, saveFile);
    }

    private void writeInputToFile(Input input, File saveFile) throws IOException{
        try (ObjectOutputStream out = new ObjectOutputStream(new BufferedOutputStream(new FileOutputStream(saveFile)))) {
            out.writeInt(input.size());
            if(input instanceof Iterable){
                for (Integer b : ((Iterable<Integer>) input)) {
                    assert (b >= 0 && b < 256);
                    out.write(b);
                }
            }else if(input instanceof LinearInput){
                ShortIterator iter = ((LinearInput) input).shortIterator();
                while(iter.hasNext()){
                    short b = iter.next();
                    assert (b >= 0 && b < 256);
                    out.write((int) b);
                }
            }
            out.writeObject(input.instructions);
            out.writeObject(input.stringEqualsHints);
            out.writeObject(input.appliedTargetedHints);

            out.writeInt(input.offsetOfLastHintAdded);
            out.writeObject(input.allInstructions);
            out.writeObject(input.allStringEqualsHints);

            /** Also write out some book-keeping info, maybe useful for analysis later **/
            out.writeInt(input.parentInputIdx);
            out.writeObject(input.seedSource);
            out.writeObject(input.mutationType);
            out.writeInt(input.numGlobalDictionaryHintsApplied);
            out.writeInt(input.numHintsAppliedThisRound);
            out.writeInt(input.numMutations);
            out.writeLong(System.currentTimeMillis() - this.campaignStartTime);
            out.writeLong(this.numTrials);
            out.writeLong(extendedDictionarySize);
        }
    }

    private void saveInputToDisk(File f, Object o) throws IOException {
        if (o instanceof Document) {
            try {
                TransformerFactory tf = TransformerFactory.newInstance();
                Transformer transformer = null;
                transformer = tf.newTransformer();
                transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "no");
                transformer.setOutputProperty(OutputKeys.METHOD, "xml");
                transformer.setOutputProperty(OutputKeys.INDENT, "yes");
                transformer.setOutputProperty(OutputKeys.ENCODING, "UTF-8");
                transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "4");

                try (PrintWriter pw = new PrintWriter(new FileWriter(f))) {
                    transformer.transform(new DOMSource((Document) o), new StreamResult(pw));
                }
            } catch (TransformerException e) {
                e.printStackTrace();
            }
        } else if (o instanceof JavaClass) {
            JavaClass jc = (JavaClass) o;
            jc.dump(f);
        } else {
            try (PrintWriter pw = new PrintWriter(new FileWriter(f))) {
                pw.println(o.toString());
            }
        }
    }

    private void saveCurrentInput(IntHashSet responsibilities, String why) throws IOException {

        // First, save to disk (note: we issue IDs to everyone, but only write to disk  if valid)
        int newInputIdx = numSavedInputs++;
        String saveFileName = String.format("id_%06d", newInputIdx);
        //if(StringEqualsHintingInputStream.hintUsedInCurrentInput){
        //    saveFileName = "HINTS_"+saveFileName;
        //}
        String how = currentInput.desc;
        File saveFile = new File(savedInputsDirectory, saveFileName);
        if (SAVE_ONLY_VALID == false || currentInput.valid) {
            writeCurrentInputToFile(saveFile);
            infoLog("Saved - %s %s %s", saveFile.getPath(), how, why);
        }

        File argsFile = new File(savedInputsDirectory, saveFileName + ".input");
        if (args != null) //todo why does this happen?
            for (Object o : args)
                saveInputToDisk(argsFile, o);

        // If not using guidance, do nothing else
        if (TOTALLY_RANDOM) {
            return;
        }


        // begin fuzzing z3 hints immediately...
        if(why.contains("hint")) {

            //currentParentInputIdx = savedInputs.size()-2;

            currentInput.desc = "hint";

        }


        // Second, save to queue
        savedInputs.add(currentInput);



        // Third, store basic book-keeping data
        currentInput.id = newInputIdx;
        currentInput.saveFile = saveFile;
        //currentInput.coverage = new Coverage(runCoverage);
        currentInput.nonZeroCoverage = runCoverage.getNonZeroCount();
        currentInput.offspring = 0;
        savedInputs.get(currentParentInputIdx).offspring += 1;

        // Fourth, assume responsibility for branches
        currentInput.responsibilities = responsibilities;
        IntIterator iter = responsibilities.intIterator();
        while(iter.hasNext()){
            int b = iter.next();
            // If there is an old input that is responsible,
            // subsume it
            Input oldResponsible = responsibleInputs.get(b);
            if (oldResponsible != null) {
                oldResponsible.responsibilities.remove(b);
                // infoLog("-- Stealing responsibility for %s from input %d", b, oldResponsible.id);
            } else {
                // infoLog("-- Assuming new responsibility for %s", b);
            }
            // We are now responsible
            responsibleInputs.put(b, currentInput);
        }


        // Fifth, map executions to input locations for splicing
        mapEcToInputLoc(currentInput);


        if (priorityQueueConfig.usePriorityQueue && central != null) {
            currentInput.calculateScore(StringEqualsHintingInputStream.getHints());
            savedInputsAccess.add(currentInput);

            List<Coordinator.Input> newScoreInputs = central.getScoreUpdates();

            Input temp = null;
            for(Coordinator.Input n : newScoreInputs) {
                for (Input i : savedInputsAccess) {
                    if (n.id == i.id){
                       temp = i;
                       break;
                    }
                }
                if(temp != null) {
                    savedInputsAccess.remove(temp);
                    temp.score += n.score;
                    savedInputsAccess.add(temp);
                }
            }


        }
    }

    private void mapEcToInputLoc(Input input) {
        if (input instanceof MappedInput) {
            MappedInput mappedInput = (MappedInput) input;
            for (int offset = 0; offset < mappedInput.size(); offset++) {
                ExecutionIndex ei = mappedInput.orderedKeys.get(offset);
                ExecutionContext ec = new ExecutionContext(ei);
                ecToInputLoc.get(ec).add(new InputLocation(mappedInput, offset));
            }
        }

    }


    @Override
    public Consumer<TraceEvent> generateCallBack(Thread thread) {

        if( thread.getName().endsWith("main")) {
            appThread = thread;
            return this::handleEvent;
        }

        else return this.emptyEvent;

    }

    private void handleEvent(TraceEvent e) {
        // Set last event to this event
        lastEvent = e;

        // Update execution indexing logic
        if (!DISABLE_EXECUTION_INDEXING) {
            e.applyVisitor(this);
        }

        // Collect totalCoverage
        runCoverage.handleEvent(e);
        // Check for possible timeouts every so often
        if (this.singleRunTimeoutMillis > 0 &&
                this.runStart != null && (++this.branchCount) % 10_000 == 0) {
            long elapsed = new Date().getTime() - runStart.getTime();
            if (elapsed > this.singleRunTimeoutMillis) {
                throw new TimeoutException(elapsed, this.singleRunTimeoutMillis);
            }
        }
    }

    @Override
    public void visitCallEvent(CallEvent c) {
        eiState.pushCall(c);
    }

    @Override
    public void visitReturnEvent(ReturnEvent r) {
        eiState.popReturn(r);
    }

    /**
     * Returns a reference to the coverage statistics.
     * @return a reference to the coverage statistics
     */
    public Coverage getTotalCoverage() {
        return totalCoverage;
    }

    /**
     * A candidate or saved test input that maps objects of type K to bytes.
     */
    public static abstract class Input<K> {

        public SeedSource seedSource;

        public int bonusMutations;

        public int numHintsAppliedThisRound;
        public int hintsRemaining;
        public int numGlobalDictionaryHintsApplied;
        public int numMutations;
        public int parentInputIdx; //right now only set post-hoc when analyzing a saved corpus

        /**
         * The file where this input is saved.
         *
         * <p>This field is null for inputs that are not saved.</p>
         */
        File saveFile = null;

        /**
         * An ID for a saved input.
         *
         * <p>This field is -1 for inputs that are not saved.</p>
         */
        public int id;

        /**
         * The description for this input.
         *
         * <p>This field is modified by the construction and mutation
         * operations.</p>
         */
        String desc;

        /**
         * The run coverage for this input, if the input is saved.
         *
         * <p>This field is null for inputs that are not saved.</p>
         */
        //This field was written to but never read: bad news when we have lots of inputs saved!
        //Coverage coverage = null;

        /**
         * The number of non-zero elements in `coverage`.
         *
         * <p>This field is -1 for inputs that are not saved.</p>
         *
         * <p></p>When this field is non-negative, the information is
         * redundant (can be computed using {@link Coverage#getNonZeroCount()}),
         * but we store it here for performance reasons.</p>
         */
        int nonZeroCoverage = -1;

        /**
         * The number of mutant children spawned from this input that
         * were saved.
         *
         * <p>This field is -1 for inputs that are not saved.</p>
         */
        int offspring = -1;

        /**
         * Whether this input resulted in a valid run.
         */
        boolean valid = false;

        /**
         * The set of coverage keys for which this input is
         * responsible.
         *
         * <p>This field is null for inputs that are not saved.</p>
         *
         * <p>Each coverage key appears in the responsibility set
         * of exactly one saved input, and all covered keys appear
         * in at least some responsibility set. Hence, this list
         * needs to be kept in-sync with {@link #responsibleInputs}.</p>
         */
        IntHashSet responsibilities = null;


        /**
         * CONFETTI
         * These are hints that must be followed to reproduce *this* input
         * stringEqualsHints and instructions are parallel arrays, each "instruction" is 2 ints: first is the offset
         * to provide a hint at, the second is the number of bytes read to select the hint.
         *
         * This design could be simplified to simply provide the right string at the right place. There will now only be
         * a single string hint for each offset, so there's no need to make that be an array.
         */
        public LinkedList<Coordinator.StringHint[]> stringEqualsHints = new LinkedList<>();
        public LinkedList<int[]> instructions = new LinkedList<>();
        public LinkedList<Coordinator.StringHintGroup> stringHintGroupsToTryInChildren = new LinkedList<>();
        public LinkedList<Coordinator.TargetedHint> appliedTargetedHints = new LinkedList<>();
        public LinkedList<Coordinator.TargetedHint> targetedHintsToTryInChildren = new LinkedList<>();


        public void updateHintsRemainingCount(){
            this.hintsRemaining = 0;
            if(this.stringEqualsHintsToTryInChildren != null)
            {
                for(Object h : this.stringEqualsHintsToTryInChildren){
                    if(h != null)
                        this.hintsRemaining += ((Coordinator.StringHint[]) h).length;
                }
            }
        }
        public Coordinator.StringHint getHintForPosition(int start, int length){
            for(int i = 0 ; i < instructions.size(); i++){
                int[] d = instructions.get(i);
                if(d[0] == start && d[1] == length){
                    return stringEqualsHints.get(i)[0];
                }
            }
            return null;
        }

        /**
         * CONFETTI
         * These are hints that were derived by Knarr from this input. They should each be tried when we generate children
         * of this input. Each hint should be tried independently, since they were all constructed from *this* input, and not
         * from a combination. If a combination would be useful, we'll generate that combo eventually anyway when the derived
         * input (with one of the hints) is analyzed again by Knarr.
         */
        public LinkedList<Coordinator.StringHint[]> stringEqualsHintsToTryInChildren;
        public LinkedList<int[]> instructionsToTryInChildren;

        public LinkedList<Coordinator.StringHint[]> allStringEqualsHints;
        public LinkedList<int[]> allInstructions;

        /**
         * CONFETTI
         * OK, so we will actually try combinations of hints directly, too - testing demonstrated that adding a single hint
         * may not be enough to reveal a new branch (so that input wouldn't be saved and mutated again). Adding multiple
         * hints at once does seem useful.
         *
         * We handle this two ways: If there are less than 10 hint positions, we will generate all combinations of hints,
         * then shuffle that list of combinations, then apply them one-by-one. When we run out of combinations, we're done.
         *
         * If there are more than 10 hint positions, generating all of the combinations (and testing them) becomes much
         * more time intensive - and at some point, we will definitely not get to trying all combinations anyway. In those
         * cases, we'll just apply random hints for each mutation.
         */
        public List<Coordinator.StringHintGroup> allStringEqualsHintsCombinations;
        int idxOfNextStringHintGroupToTry;

        public HashMap<int[], ArrayList<Coordinator.StringHint>> allStringEqualsHintsByOffset;
        public List<int[]> allUniqueHintPositions;


        public void organizeStringHintsForCombinations(){
            if(this.allStringEqualsHints == null)
                return;
            Iterator<Coordinator.StringHint[]> hintIter = allStringEqualsHints.iterator();
            Iterator<int[]> insnIter = allInstructions.iterator();

            if(this.allInstructions.size() < 10) {
                allStringEqualsHintsCombinations = new LinkedList<>();

                List<HintChoice> allHintChoices = new ArrayList<>();
                /**
                 * Surely there is a better algorithm to do this more efficiently. What we do here is generate all combinations
                 * of all string hints (even when applying multiple to the same location which makes no sense), and then filter
                 * out the combinations that have multiple hints applied at the same location.
                 *
                 */
                while (insnIter.hasNext()) {
                    int[] insn = insnIter.next();
                    Coordinator.StringHint[] hints = hintIter.next();
                    for (Coordinator.StringHint hint : hints) {
                        allHintChoices.add(new HintChoice(insn, hint));
                    }
                }

                IntHashSet insnInThisCombi = new IntHashSet();

                for (int numberHintsToApply = 2; numberHintsToApply <= allInstructions.size(); numberHintsToApply++) {
                    List<List<HintChoice>> combis = Generator.combination(allHintChoices).simple(numberHintsToApply).stream()
                            .collect(Collectors.toList());
                    for (List<HintChoice> combination : combis) {
                        insnInThisCombi.clear();
                        boolean isOK = true;
                        Coordinator.StringHintGroup hg = new Coordinator.StringHintGroup();
                        for (HintChoice hc : combination) {
                            if (!insnInThisCombi.add(hc.insn[0])) {
                                isOK = false;
                            } else {
                                hg.hints.add(hc.hint);
                                hg.instructions.add(hc.insn);
                            }
                        }
                        if (isOK)
                            allStringEqualsHintsCombinations.add(hg);
                    }
                }
                Collections.shuffle(allStringEqualsHintsCombinations);
            }else{
                //Prepare to randomly apply hints
                allStringEqualsHintsByOffset = new HashMap<>();
                while(insnIter.hasNext()){
                    int[] insn = insnIter.next();
                    Coordinator.StringHint[] hints = hintIter.next();
                    if(!allStringEqualsHintsByOffset.containsKey(insn)){
                        allStringEqualsHintsByOffset.put(insn, new ArrayList<>());
                    }
                    for(Coordinator.StringHint hint : hints){
                        allStringEqualsHintsByOffset.get(insn).add(hint);
                    }
                }
                this.allUniqueHintPositions = new ArrayList<>(allStringEqualsHintsByOffset.keySet());
            }
        }


        static class HintChoice {
            int[] insn;
            Coordinator.StringHint hint;

            public HintChoice(int[] insn, Coordinator.StringHint hint) {
                this.insn = insn;
                this.hint = hint;
            }
        }



        public boolean alreadyReceivedHints;

        /**
         * CONFETTI
         * These are bytes that we found in any constraints in the SUT, be they from strings or otherwise.
         */
        public HashSet<Integer> bytesFoundUsedInSUT;

        /**
         * A tunable "score" of how "interesting" the input is
         */
        public Integer score = 0;

        boolean z3 = false;

        protected int offsetOfLastHintAdded = -1;

        public MutationType mutationType;
        public int lastFuzzedCycle = -1;

        /**
         * Create an empty input.
         */
        public Input() {
            desc = "random";
        }

        /**
         * Create a copy of an existing input.
         *
         * @param toClone the input map to clone
         */
        public Input(Input toClone) {
            desc = String.format("src:%06d", toClone.id);
            this.stringEqualsHints = new LinkedList<>(toClone.stringEqualsHints);
            this.instructions = new LinkedList<>(toClone.instructions);
            this.offsetOfLastHintAdded = toClone.offsetOfLastHintAdded;
            this.seedSource = toClone.seedSource;
        }

        public abstract int getOrGenerateFresh(K key, Random random);
        public abstract int size();
        public abstract Input fuzz(Random random);
        public abstract void gc();


        private  void calculateScore(LinkedList<Coordinator.StringHint[]> hints) {

            Integer temp_score = 0;
            if(this.valid) {
                for (int i = 0; i < this.responsibilities.size(); i++)
                    temp_score = ZestGuidance.priorityQueueConfig.validInputScoreOperation.operation(temp_score, ZestGuidance.priorityQueueConfig.validInputScoreValue);
            }
            if(this.isFavored())
                temp_score = ZestGuidance.priorityQueueConfig.favoredInputScoreOperation.operation(temp_score, ZestGuidance.priorityQueueConfig.favoredInputScoreValue);
            for(Coordinator.StringHint[] stringHints : hints ) {
                for(int i = 0; i < stringHints.length; i++) {
                    if(stringHints[i].getType() == Coordinator.HintType.Z3) {
                        temp_score = ZestGuidance.priorityQueueConfig.z3HintScoreOperation.operation(temp_score, ZestGuidance.priorityQueueConfig.z3HintScoreValue);
                    }
                    else
                        temp_score = ZestGuidance.priorityQueueConfig.equalsHintScoreOperation.operation(temp_score, ZestGuidance.priorityQueueConfig.equalsHintScoreValue);
                }
            }
            if(this.isZ3()) {

                for(int i = 0; i < this.responsibilities.size(); i++)
                    temp_score = ZestGuidance.priorityQueueConfig.z3newBranchesScoreOperation.operation(temp_score, ZestGuidance.priorityQueueConfig.z3newBranchesScoreValue);
            }

            //occasionally just randomly shoot something up to the front (1/500)


            this.score = temp_score;
        }
        /**
         * Returns whether this input should be favored for fuzzing.
         *
         * <p>An input is favored if it is responsible for covering
         * at least one branch.</p>
         *
         * @return
         */
        private boolean isFavored() {
            return responsibilities != null && responsibilities.size() > 0;
        }

        private boolean isZ3() { return z3;}

        /**
         * Sample from a geometric distribution with given mean.
         *
         * Utility method used in implementing mutation operations.
         *
         * @param random a pseudo-random number generator
         * @param mean the mean of the distribution
         * @return a randomly sampled value
         */
        protected static int sampleGeometric(Random random, double mean) {
            double p = 1 / mean;
            double uniform = random.nextDouble();
            return (int) ceil(log(1 - uniform) / log(1 - p));
        }

        public void addSingleHintInPlace(Coordinator.StringHint hint, int[] insn) {
            if(hint.getType() == Coordinator.HintType.LENGTH){
                //TODO come back and implement some mutation for this...
                return;
            }
            if(this.instructions == null || this.stringEqualsHints == null){
                this.instructions = new LinkedList<>();
                this.stringEqualsHints = new LinkedList<>();
            }
            if(this.instructions.isEmpty()){
                this.instructions.add(insn);
                this.stringEqualsHints.add(new Coordinator.StringHint[]{hint});
                return;
            }
            Iterator<Coordinator.StringHint[]> newInputHintIter = this.stringEqualsHints.iterator();
            Iterator<int[]> newInputInsnIter = this.instructions.iterator();
            int pos = 0;
            boolean inserted = false;
            while(newInputInsnIter.hasNext()){
                newInputHintIter.next();
                int[] insns = newInputInsnIter.next();
                if(insns[0] == insn[0]){
                    inserted = true;
                    this.stringEqualsHints.set(pos, new Coordinator.StringHint[]{hint});
                    break;
                }
                if(insns[0] > insn[0]){
                    inserted = true;
                    this.stringEqualsHints.add(pos, new Coordinator.StringHint[]{hint});
                    this.instructions.add(pos, insn); // TODO should we clear hints after the one that we inserted??? probably before we send it to knar...
                    break;
                }
                pos++;
            }
            if(!inserted){
                this.stringEqualsHints.add(new Coordinator.StringHint[]{hint});
                this.instructions.add(insn);
            }
            this.offsetOfLastHintAdded = insn[0]+insn[1];
        }

        protected void clearHintsAfterOffset(int offset){
            Iterator<Coordinator.StringHint[]> hintIter = this.stringEqualsHints.iterator();
            Iterator<int[]> insnIter = this.instructions.iterator();
            while(hintIter.hasNext()){
                int[] insn = insnIter.next();
                hintIter.next();

                if(insn[0] + insn[1]> offset){
                    hintIter.remove();
                    insnIter.remove();
                }
            }
        }

        public void addExtraRandomStringEqualsHints(Random random) {
            for(int i = 0; i < this.stringEqualsHintsToTryInChildren.size(); i++) {
                Coordinator.StringHint[] hints = this.stringEqualsHintsToTryInChildren.get(i);
                if(hints.length > 0) {
                    Coordinator.StringHint[] extraHinted = new Coordinator.StringHint[hints.length + 1];
                    System.arraycopy(hints, 0, extraHinted, 0, hints.length);
                    StringBuilder sb = new StringBuilder(random.nextInt(50) + 5);
                    for (int j = 0; j < sb.capacity(); j++) {
                        sb.append((char)(48 + random.nextInt(127 - 48)));
                    }
                    extraHinted[hints.length] = new Coordinator.StringHint(sb.toString(), Coordinator.HintType.EQUALS, null);
                    this.stringEqualsHintsToTryInChildren.set(i, extraHinted);
                }
            }
        }
    }

    private static long mutatedBytes = 0L;

    public enum SeedSource {
        RANDOM,
        HINTS,
        Z3
    }

    public enum MutationType {
        RANDOM,
        APPLY_SINGLE_HINT,
        APPLY_Z3_HINT,
        //BEFORE_HINTS,
        //AFTER_HINTS,
        TARGETED_RANDOM,
        //AFTER_HINTS_BUT_NEAR,
        APPLY_Z3_HINT_EXTENDED, APPLY_SINGLE_CHAR_HINT,
        APPLY_MULTIPLE_HINTS;
    }

    public static class LinearInput extends Input<Integer> {

        /** A list of byte values (0-255) ordered by their index. */
        public ShortArrayList values;
        //Note: Would save more space if this were a ByteArrayList, but the code as I found it
        //used an ArrayList<Integer> (and assumed all bytes were unsigned), so there would be more
        //refactoring needed to migrate to actual byte types, this gives a savings enough from avoiding
        //primitive boxing, at least.

        /** The number of bytes requested so far */
        protected int requested = 0;




        public LinearInput() {
            super();
            this.values = new ShortArrayList();
        }

        public LinearInput(LinearInput other) {
            super(other);
            this.values = new ShortArrayList(other.values.size());
            this.values.addAll(other.values);
        }

        public void reset(){
            this.requested = 0;
        }

        public static LinearInput fromFile(File f) throws IOException, ClassNotFoundException {
            LinearInput ret = new LinearInput();
            try(ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(new FileInputStream(f)))){
                int size = ois.readInt();
                for(int i = 0; i < size; i++){
                    ret.values.add((short) ois.read());
                }
                ret.instructions = (LinkedList<int[]>) ois.readObject();
                ret.stringEqualsHints = (LinkedList<Coordinator.StringHint[]>) ois.readObject();
                ret.appliedTargetedHints = (LinkedList<Coordinator.TargetedHint>) ois.readObject();
                ret.offsetOfLastHintAdded = ois.readInt();
                ret.allInstructions = (LinkedList<int[]>) ois.readObject();
                ret.allStringEqualsHints = (LinkedList<Coordinator.StringHint[]>) ois.readObject();
                ret.parentInputIdx = ois.readInt();
                ret.seedSource = (SeedSource) ois.readObject();
                ret.mutationType = (MutationType) ois.readObject();
                ret.numGlobalDictionaryHintsApplied = ois.readInt();
                ret.numHintsAppliedThisRound = ois.readInt();
                ret.numMutations = ois.readInt();
                ret.id = Integer.parseInt(f.getName().substring(3));
                //TODO do we need these?
                long execTime  =ois.readLong();
                long numTrials = ois.readLong();
                long extendedDictSize = ois.readLong();
            }
            return ret;
        }

        @Override
        public int getOrGenerateFresh(Integer key, Random random) {
            // Don't generate over the limit
            if (requested >= MAX_INPUT_SIZE) {
                return -1;
            }

            // Otherwise, make sure we are requesting just beyond the end-of-list
            // assert (key == values.size());
            if (key != requested) {
                throw new GuidanceException(String.format("Bytes from linear input out of order. " +
                        "Size = %d, Key = %d", values.size(), key));
            }

            // If it exists in the list, return it
            if (key < values.size()) {
                requested++;
                // infoLog("Returning old byte at key=%d, total requested=%d", key, requested);
                return values.get(key);
            }

            // Handle end of stream
            if (GENERATE_EOF_WHEN_OUT) {
                return -1;
            } else {
                // Just generate a random input
                short val = (short) random.nextInt(256);
                values.add(val);
                requested++;
                // infoLog("Generating fresh byte at key=%d, total requested=%d", key, requested);
                return val;
            }
        }

        @Override
        public int size() {
            return values.size();
        }

        /**
         * Truncates the input list to remove values that were never actually requested.
         *
         * <p>Although this operation mutates the underlying object, the effect should
         * not be externally visible (at least as long as the test executions are
         * deterministic).</p>
         */
        @Override
        public void gc() {
            // Remove elements beyond "requested"
            ShortArrayList old = values;
            if(requested != old.size()) {
                values = new ShortArrayList(requested);
                for (int i = 0; i < old.size(); i++)
                    values.add(old.get(i));
                values.trimToSize();
            }
        }

        @Override
        public Input fuzz(Random random) {
            // Clone this input to create initial version of new child
            LinearInput newInput = new LinearInput(this);

            boolean setToZero = random.nextDouble() < 0.1; // one out of 10 times
            boolean skipHints = INCLUDE_SINGLE_HINTS_AS_BONUS_MUTATIONS && this.numHintsAppliedThisRound > this.bonusMutations;
            if(!skipHints && !this.stringHintGroupsToTryInChildren.isEmpty()
                    && (INCLUDE_SINGLE_HINTS_AS_BONUS_MUTATIONS || random.nextBoolean())
            ){
                //Before doing any random mutations or one-off hints, first try to apply any SETS of hints that we have
                //The main source of these right now is from one-off character adding for Z3 inputs
                Coordinator.StringHintGroup hints = this.stringHintGroupsToTryInChildren.removeLast();
                newInput.desc += ",z3ExtendedHints";
                newInput.mutationType = MutationType.APPLY_Z3_HINT_EXTENDED;
                newInput.seedSource = SeedSource.Z3;
                infoLog("Applied hint: %s", newInput.desc);
                newInput.instructions = hints.instructions;
                newInput.stringEqualsHints = new LinkedList<>();
                for(Coordinator.StringHint h : hints.hints){
                    newInput.stringEqualsHints.add(new Coordinator.StringHint[]{h});
                }
                this.numHintsAppliedThisRound++;
                return newInput;

            }
            else if(!skipHints && this.instructionsToTryInChildren != null && !this.instructionsToTryInChildren.isEmpty()
                    && (INCLUDE_SINGLE_HINTS_AS_BONUS_MUTATIONS || random.nextBoolean()))
            {
                // Before doing any random mutations, first try to generate a new input that simply uses one of the hints
                // We'll try each hint independently, and only once: if it's useful, then a new input can be derived from
                // that one, which will always use that hint.

                Coordinator.StringHint[] hints = this.stringEqualsHintsToTryInChildren.peek();
                int[] insn = this.instructionsToTryInChildren.peek();
                Coordinator.StringHint hint;
                if(hints.length == 0){ //TODO what the heck causes this!?
                    this.stringEqualsHintsToTryInChildren.pop();
                    this.instructionsToTryInChildren.pop();
                    if(insn.length == 2){
                        //Just to be cute, let's keep it as-is but do a single random mutation at the location indicated
                        //if this check fails, then we just do a random mutation
                        newInput.desc += ",guidedMutation@" + insn[0];
                        for(int i = insn[0]; i < insn[0]+insn[1]; i++){
                            int mutatedValue = setToZero ? 0 : random.nextInt(256);
                            mutatedBytes += Integer.BYTES;
                            newInput.values.set(i, (short) mutatedValue);
                        }
                        newInput.mutationType = MutationType.TARGETED_RANDOM;
                        newInput.seedSource = SeedSource.RANDOM;
                        this.numHintsAppliedThisRound++;
                        return newInput;
                    }
                }
                else {
                    if (hints.length == 1) {
                        hint = hints[0];
                        this.stringEqualsHintsToTryInChildren.pop();
                        this.instructionsToTryInChildren.pop();
                    } else {
                        hint = hints[0];
                        Coordinator.StringHint[] remainingStringHints = new Coordinator.StringHint[hints.length - 1];
                        System.arraycopy(hints, 1, remainingStringHints, 0, remainingStringHints.length);
                        this.stringEqualsHintsToTryInChildren.set(0, remainingStringHints);
                    }
                    for (int i = 0; i < countOfInputsSavedWithMutationCountsRanges.length; i++) {
                        if (1 <= countOfInputsSavedWithMutationCountsRanges[i]) {
                            countOfInputsCreatedWithHintMutationCounts[i]++;
                            break;
                        }
                    }
                    newInput.numMutations = 1;
                    newInput.desc += ",hint:" + hint.getType() + "=" + hint.getHint() + "@" + insn[0];
                    newInput.mutationType = MutationType.APPLY_SINGLE_HINT;
                    newInput.seedSource = SeedSource.HINTS;
                    infoLog("Applied hint: %s", newInput.desc);
                    newInput.addSingleHintInPlace(hint, insn);
                    if(hint.getType() == Coordinator.HintType.CHAR)
                        newInput.mutationType = MutationType.APPLY_SINGLE_CHAR_HINT;

                    this.numHintsAppliedThisRound++;
                    return newInput;
                }
            }
            //if(newInput.stringEqualsHints != null){
            //    for(Coordinator.StringHint[] sh : newInput.stringEqualsHints){
            //        if(sh.length > 0 && sh[0].getHint().equals("execution")){
            //            System.out.println("We are mutating one that already has execution");
            //        }
            //        if(sh.length>1){
            //            throw new IllegalStateException();
            //        }
            //    }
            //}


            /*
            This should only be possible after we've fuzzed this input at least once with random mutations.
            We pregenerate the combinations of hints, shuffle them, and store them in a list.
            Then, we pop from that list while fuzzing so that we only try each combination once.
            There are plenty of inputs with say, only 5 hints in them: and we can easily exhaustively try them, and when
            we finish with that, we should STOP rerunning the same exact random combinations!!!
             */
            if(this.allStringEqualsHintsCombinations != null && this.idxOfNextStringHintGroupToTry < this.allStringEqualsHintsCombinations.size() && random.nextBoolean()) {
                Coordinator.StringHintGroup combi = this.allStringEqualsHintsCombinations.get(this.idxOfNextStringHintGroupToTry);
                this.idxOfNextStringHintGroupToTry++;
                newInput.numMutations = combi.hints.size();
                newInput.desc += ",hintHavoc:" + numMutations;
                newInput.mutationType = MutationType.APPLY_MULTIPLE_HINTS;
                newInput.seedSource = SeedSource.HINTS;
                int n = newInput.numMutations;
                for (int i = 0; i < countOfInputsSavedWithMutationCountsRanges.length; i++) {
                    if (n <= countOfInputsSavedWithMutationCountsRanges[i]) {
                        countOfInputsCreatedWithHintMutationCounts[i]++;
                        break;
                    }
                }
                Iterator<Coordinator.StringHint> hintIterator = combi.hints.iterator();
                Iterator<int[]> insnIterator = combi.instructions.iterator();
                while(hintIterator.hasNext()){
                    newInput.addSingleHintInPlace(hintIterator.next(), insnIterator.next());
                }
            } else if (this.allStringEqualsHintsByOffset != null && random.nextInt(10) == 1) { /* 10% chance of doign multi-hint only mutation */
                int numMutations = sampleGeometric(random, this.allStringEqualsHintsByOffset.size()/2);
                if(numMutations == 0){
                    numMutations = 1;
                }
                if(numMutations > this.allUniqueHintPositions.size()){
                    numMutations = this.allUniqueHintPositions.size();
                }
                newInput.numMutations = numMutations;
                newInput.desc += ",hintHavoc:" + numMutations;
                newInput.seedSource = SeedSource.HINTS;
                newInput.mutationType = MutationType.APPLY_MULTIPLE_HINTS;
                int n = newInput.numMutations;
                for (int i = 0; i < countOfInputsSavedWithMutationCountsRanges.length; i++) {
                    if (n <= countOfInputsSavedWithMutationCountsRanges[i]) {
                        countOfInputsCreatedWithHintMutationCounts[i]++;
                        break;
                    }
                }

                for(int mutation = 0; mutation <= numMutations; mutation++){
                    int idxToApplyHintAt = random.nextInt(this.allUniqueHintPositions.size());
                    int[] insn = this.allUniqueHintPositions.get(idxToApplyHintAt);
                    ArrayList<Coordinator.StringHint> hintsAtThisLocation = this.allStringEqualsHintsByOffset.get(insn);
                    int hintToUse = random.nextInt(hintsAtThisLocation.size());
                    newInput.addSingleHintInPlace(hintsAtThisLocation.get(hintToUse), insn);
                }
            } else {
                // Use the "normal" zest mutator
                // Stack a bunch of mutations
                int numMutations = sampleGeometric(random, MEAN_MUTATION_COUNT);
                newInput.numMutations = numMutations;
                newInput.desc += ",havoc:" + numMutations;
                int n = newInput.numMutations;
                for (int i = 0; i < countOfInputsSavedWithMutationCountsRanges.length; i++) {
                    if (n <= countOfInputsSavedWithMutationCountsRanges[i]) {
                        countOfInputsCreatedWithMutationCounts[i]++;
                        break;
                    }
                }

                int mutateOnlyAfter = 0;
                int mutateOnlyBefore = newInput.values.size();
                //if (this.offsetOfLastHintAdded >= 0) {
                //    if (random.nextBoolean()) {
                //        // Also constrain how far out we look for mutations to stay close to this hint.
                //        mutateOnlyAfter = this.offsetOfLastHintAdded;
                //        mutateOnlyBefore = this.offsetOfLastHintAdded + 40;
                //        if (mutateOnlyAfter >= newInput.values.size()) {
                //            mutateOnlyAfter = 0;
                //        }
                //        if (mutateOnlyBefore >= newInput.values.size()) {
                //            mutateOnlyBefore = newInput.values.size();
                //        }
                //        newInput.desc += ",afterHint:" + this.offsetOfLastHintAdded + ",before:" + mutateOnlyBefore;
                //        newInput.mutationType = MutationType.AFTER_HINTS_BUT_NEAR;
                //
                //    } else if (random.nextBoolean()) {
                //        // If adding a hint was useful for this input (that is - it resulted in the input
                //        // being saved), then we will apply half of the mutations *after* that hint,
                //        // rather than before
                //        mutateOnlyAfter = this.offsetOfLastHintAdded;
                //        newInput.desc += ",afterHint:" + this.offsetOfLastHintAdded;
                //        if (mutateOnlyAfter >= newInput.values.size()) {
                //            //Hmm... not sure what to do here.
                //            mutateOnlyAfter = 0;
                //        }
                //        newInput.mutationType = MutationType.AFTER_HINTS;
                //    } else {
                //        newInput.mutationType = MutationType.RANDOM;
                //    }
                //} else {
                    newInput.mutationType = MutationType.RANDOM;
                //}

                for (int mutation = 1; mutation <= numMutations; mutation++) {

                    int offset;
                    int mutationSize;

                    // Select a random offset and size
                    offset = random.nextInt(mutateOnlyBefore - mutateOnlyAfter) + mutateOnlyAfter;
                    mutationSize = sampleGeometric(random, MEAN_MUTATION_SIZE);


                    //If the mutation is before any hints in the input, remove the hints.
                    if (!newInput.instructions.isEmpty()) {
                        newInput.clearHintsAfterOffset(offset);
                    }


                    // desc += String.format(":%d@%d", mutationSize, idx);

                    // Mutate a contiguous set of bytes from offset
                    for (int i = offset; i < offset + mutationSize; i++) {
                        // Don't go past end of list
                        if (i >= newInput.values.size()) {
                            break;
                        }

                        // Otherwise, apply a random mutation
                        int mutatedValue = setToZero ? 0 : random.nextInt(256);
                        mutatedBytes += Integer.BYTES;
                        newInput.values.set(i, (short) mutatedValue);
                    }
                }
            }
            return newInput;
        }

        public ShortIterator shortIterator() {
            return values.shortIterator();
        }
    }


    /**
     * A candidate test input represented as a map from execution indices
     * to integer values.
     *
     * <p>When a quickcheck-like generator requests a new ``random'' byte,
     * the current execution index is used to retrieve the input from
     * this input map (a fresh value is generated and stored in the map
     * if the key is not mapped).</p>
     *
     * <p>Inputs should not be publicly mutable. The only way to mutate
     * an input is via the {@link #fuzz} method which produces a new input
     * object with some values mutated.</p>
     */
    public class MappedInput extends Input<ExecutionIndex> {

        /**
         * Whether this input has been executed.
         *
         * When this field is {@code false}, the field {@link #orderedKeys}
         * is not yet populated and must not be used. When this field is {@code true},
         * the input should be considered immutable and neither {@link #orderedKeys} nor
         * {@link #valuesMap} must be modified.
         */
        protected boolean executed = false;

        /** A map from execution indexes to the byte (0-255) to be returned at that index. */
        protected LinkedHashMap<ExecutionIndex, Integer> valuesMap;

        /**
         * A list of execution indexes that are actually requested by the test program when
         * executed with this input.
         *
         * <p>This list is initially empty, and is populated at the end of the run, after which
         * it is frozen. The list of keys are in order of their occurrence in the execution
         * trace and can therefore be used to serialize the map into a sequence of bytes.</p>
         *
         */
        protected ArrayList<ExecutionIndex> orderedKeys = new ArrayList<>();


        private List<InputPrefixMapping> demandDrivenSpliceMap = new ArrayList<>();

        /**
         * Create an empty input map.
         */
        public MappedInput() {
            super();
            valuesMap = new LinkedHashMap<>();
        }

        /**
         * Create a copy of an existing input map.
         *
         * @param toClone the input map to clone
         */
        public MappedInput(MappedInput toClone) {
            super(toClone);
            valuesMap = new LinkedHashMap<>(toClone.valuesMap);
        }

        /**
         * Returns the size of this input, in terms of number of bytes
         * in its value map.
         *
         * @return the size of this input
         */
        public final int size() {
            return valuesMap.size();
        }

        /**
         * Returns the byte mapped by this input at a given offset.
         *
         * @param offset the byte offset in the input
         * @return the byte value at that offset
         *
         * @throws IndexOutOfBoundsException if the offset is negative or
         *      larger than {@link #size}()-1
         * @throws IllegalStateException if this method is called before the input
         *                               has been executed
         */
        private final int getValueAtOffset(int offset) throws IndexOutOfBoundsException, IllegalStateException {
            if (!executed) {
                throw new GuidanceException("Cannot get with offset before execution");
            }

            // Return the mapping for the execution index queried at the offset
            ExecutionIndex ei = orderedKeys.get(offset);
            return valuesMap.get(ei);
        }


        /**
         * Returns the execution index mapped by this input at a given offset.
         *
         * @param offset the byte offset in the input
         * @return the execution index value at that offset
         *
         * @throws IndexOutOfBoundsException if the offset is negative or
         *      larger than {@link #size}()-1
         * @throws IllegalStateException if this method is called before the input
         *                               has been executed
         */
        private final ExecutionIndex getKeyAtOffset(int offset) throws IndexOutOfBoundsException, IllegalStateException {
            if (!executed) {
                throw new IllegalStateException("Cannot get with offset before execution");
            }

            // Return the execution index queried at the offset
            return orderedKeys.get(offset);
        }

        private InputPrefixMapping getInputPrefixMapping(ExecutionIndex ei) {
            for (InputPrefixMapping ipm : demandDrivenSpliceMap) {
                if (ei.hasPrefix(ipm.targetPrefix)) {
                    return ipm;
                }
            }
            return null;
        }


        /**
         * Retrieve a value for an execution index if mapped, else generate
         * a fresh value.
         *
         * @param key    the execution index of the trace event requesting a new byte
         * @param random the PRNG
         * @return the value to return to the quickcheck-like generator
         * @throws IllegalStateException if this method is called after the input
         *                               has been executed
         */
        @Override
        public int getOrGenerateFresh(ExecutionIndex key, Random random) throws IllegalStateException {
            if (executed) {
                throw new IllegalStateException("Cannot generate fresh values after execution");
            }

            // If we reached a limit, then just return EOF
            if (orderedKeys.size() >= MAX_INPUT_SIZE) {
                return -1;
            }

            // Try to get existing values
            Integer val = valuesMap.get(key);

            // If not, generate a new value
            if (val == null) {
                InputPrefixMapping ipm;

                // If we have an input prefix mapping for this execution index,
                // then splice from the source input
                if ((ipm = getInputPrefixMapping(key)) != null) {
                    Prefix sourcePrefix = ipm.sourcePrefix;
                    Suffix sourceSuffix = ipm.sourcePrefix.getEi().getSuffixOfPrefix(sourcePrefix);
                    ExecutionIndex sourceEi = new ExecutionIndex(sourcePrefix, sourceSuffix);
                    // The value can be taken from the source
                    val = ipm.sourceInput.getValueAtKey(sourceEi);
                }

                // If we could not splice or were unsuccessful, try to generate a new input
                if (val == null) {
                    if (GENERATE_EOF_WHEN_OUT) {
                        return -1;
                    }
                    if (random.nextDouble() < DEMAND_DRIVEN_SPLICING_PROBABILITY) {
                        // TODO: Find a random inputLocation with same EC,
                        // extract common suffix of sourceEi and targetEi,
                        // and map targetPrefix to sourcePrefix in the IPM


                    } else {
                        // Just generate a random input
                        val = random.nextInt(256);
                    }
                }

                // Put the new value into the map
                assert (val != null);

                valuesMap.put(key, val);
            }

            // Mark this key as visited
            orderedKeys.add(key);

            return val;
        }


        /**
         * Gets the byte mapped by this input at a given execution index.
         *
         * @param ei the execution index
         * @return the value mapped for this index, or {@code null} if no such mapping exists
         *
         * @throws IndexOutOfBoundsException if the offset is negative or
         *      larger than {@link #size}()-1
         */
        protected final Integer getValueAtKey(ExecutionIndex ei) throws IndexOutOfBoundsException {
            return valuesMap.get(ei);
        }

        /**
         * Sets the byte mapped by this input at a given execution index.
         *
         * @param ei  the execution index at which to insert
         * @param val the byte to insert
         *
         * @throws IndexOutOfBoundsException if the offset is negative or
         *      larger than {@link #size}()-1
         * @throws IllegalStateException if this method is called after the input
         *                               has been executed
         */
        protected final void setValueAtKey(ExecutionIndex ei, int val) throws IndexOutOfBoundsException, IllegalStateException {
            if (executed) {
                throw new IllegalStateException("Cannot set value before execution");
            }

            valuesMap.put(ei, val);
        }

        /**
         * Trims the input map of all keys that were never actually requested since
         * its construction.
         *
         * <p>Although this operation mutates the underlying object, the effect should
         * not be externally visible (at least as long as the test executions are
         * deterministic).</p>
         */
        @Override
        public void gc() {
            LinkedHashMap<ExecutionIndex, Integer> newMap = new LinkedHashMap<>();
            for (ExecutionIndex key : orderedKeys) {
                newMap.put(key, valuesMap.get(key));
            }
            valuesMap = newMap;

            // Set the `executed` flag
            executed = true;
        }

        /**
         * Return a new input derived from this one with some values
         * mutated.
         *
         * Pass-through to {@link #fuzz(Random, Map)}
         *
         */
        @Override
        public Input fuzz(Random random) {
            return fuzz(random, ZestGuidance.this.ecToInputLoc);
        }

        /**
         * Return a new input derived from this one with some values
         * mutated.
         *
         * <p>This method performs one or both of random mutations
         * and splicing.</p>
         *
         * <p>Random mutations are done by performing M
         * mutation operations each on a random contiguous sequence of N bytes,
         * where M and N are sampled from a geometric distribution with mean
         * {@link #MEAN_MUTATION_COUNT} and {@link #MEAN_MUTATION_SIZE}
         * respectively.</p>
         *
         * <p>Splicing is performed by first randomly choosing a location and
         * its corresponding execution context in this input's value map, and then
         * copying a contiguous sequence of up to Z bytes from another input,
         * starting with a location that also maps the same execution context.
         * Here, Z is sampled from a uniform distribution from 0 to
         * {@link #MAX_SPLICE_SIZE}.</p>
         *
         * @param random the PRNG
         * @return a newly fuzzed input
         */
        protected MappedInput fuzz(Random random, Map<ExecutionContext, ArrayList<InputLocation>> ecToInputLoc) {
            // Derive new input from this object as source
            MappedInput newInput = new MappedInput(this);

            // Maybe try splicing
            boolean splicingDone = false;

            // Only splice if we have been provided the ecToInputLoc
            if (ecToInputLoc != null) {

                // TODO: Do we really want splicing to be this frequent?
                if (random.nextBoolean()) {
                    final int MIN_TARGET_ATTEMPTS = 3;
                    final int MAX_TARGET_ATTEMPTS = 6;

                    int targetAttempts = MIN_TARGET_ATTEMPTS;

                    outer: for (int targetAttempt = 1; targetAttempt < targetAttempts; targetAttempt++) {

                        // Choose an execution context at which to splice at
                        // Note: We get EI and value from `this` rather than `newInput`
                        // because `this` has already been executed
                        int targetOffset = random.nextInt(newInput.valuesMap.size());
                        ExecutionIndex targetEi = this.getKeyAtOffset(targetOffset);

                        ExecutionContext targetEc = new ExecutionContext(targetEi);
                        int valueAtTarget = this.getValueAtOffset(targetOffset);

                        // Find a suitable input location to splice from
                        ArrayList<InputLocation> inputLocations = ecToInputLoc.get(targetEc);

                        // If this was a bad choice of target, try again without penalty if possible
                        if (inputLocations.size() == 0) {
                            // Try to increase the loop bound a little bit to get another chance
                            targetAttempts = Math.min(targetAttempts+1, MAX_TARGET_ATTEMPTS);
                            continue;
                        }

                        InputLocation inputLocation;

                        // Try a bunch of times
                        for (int attempt = 1; attempt <= 10; attempt++) {

                            // Get a candidate source location with the same execution context
                            inputLocation = inputLocations.get(random.nextInt(inputLocations.size()));
                            MappedInput sourceInput = inputLocation.input;
                            int sourceOffset = inputLocation.offset;


                            // Do not splice with ourselves
                            if (sourceInput == this) {
                                continue;
                            }

                            // Do not splice if the first value is the same in source and target
                            if (sourceInput.getValueAtOffset(sourceOffset) == valueAtTarget) {
                                continue;
                            }

                            int splicedBytes = 0;
                            if (!DISABLE_EXECUTION_INDEXING && SPLICE_SUBTREE) {
                                // Do not splice if there is no common suffix between EI of source and target
                                ExecutionIndex sourceEi = sourceInput.getKeyAtOffset(sourceOffset);
                                Suffix suffix = targetEi.getCommonSuffix(sourceEi);
                                if (suffix.size() == 0) {
                                    continue;
                                }

                                // Extract the source and target prefixes
                                Prefix sourcePrefix = sourceEi.getPrefixOfSuffix(suffix);
                                Prefix targetPrefix = targetEi.getPrefixOfSuffix(suffix);
                                assert (sourcePrefix.size() == targetPrefix.size());

                                // OK, this looks good. Let's splice!
                                int srcIdx = sourceOffset;
                                while (srcIdx < sourceInput.size()) {
                                    ExecutionIndex candidateEi = sourceInput.getKeyAtOffset(srcIdx);
                                    if (candidateEi.hasPrefix(sourcePrefix) == false) {
                                        // We are no more in the same sub-tree as sourceEi
                                        break;
                                    }
                                    Suffix spliceSuffix = candidateEi.getSuffixOfPrefix(sourcePrefix);
                                    ExecutionIndex spliceEi = new ExecutionIndex(targetPrefix, spliceSuffix);
                                    newInput.valuesMap.put(spliceEi, sourceInput.valuesMap.get(candidateEi));

                                    srcIdx++;
                                }
                                splicedBytes = srcIdx - sourceOffset;
                            } else {

                                int spliceSize = 1 + random.nextInt(MAX_SPLICE_SIZE);
                                int src = sourceOffset;
                                int tgt = targetOffset;
                                int srcSize = sourceInput.size();
                                int tgtSize = newInput.size();
                                while (splicedBytes < spliceSize && src < srcSize && tgt < tgtSize) {
                                    int val = sourceInput.getValueAtOffset(src);
                                    ExecutionIndex key = this.getKeyAtOffset(tgt);
                                    newInput.setValueAtKey(key, val);

                                    splicedBytes++;
                                    src++;
                                    tgt++;
                                }
                            }

                            // Complete splicing
                            splicingDone = true;
                            newInput.desc += String.format(",splice:%06d:%d@%d->%d", sourceInput.id, splicedBytes,
                                    sourceOffset, targetOffset);

                            break outer; // Stop more splicing attempts!

                        }
                    }
                }
            }

            // Maybe do random mutations
            if (splicingDone == false || random.nextBoolean()) {

                // Stack a bunch of mutations
                int numMutations = sampleGeometric(random, MEAN_MUTATION_COUNT);
                newInput.desc += ",havoc:"+numMutations;

                boolean setToZero = random.nextDouble() < 0.1; // one out of 10 times

                for (int mutation = 1; mutation <= numMutations; mutation++) {

                    // Select a random offset and size
                    int offset = random.nextInt(newInput.valuesMap.size());
                    int mutationSize = sampleGeometric(random, MEAN_MUTATION_SIZE);

                    // desc += String.format(":%d@%d", mutationSize, idx);

                    // Iterate over all entries in the value map
                    Iterator<Map.Entry<ExecutionIndex, Integer>> entryIterator
                            = newInput.valuesMap.entrySet().iterator();
                    for (int i = 0; entryIterator.hasNext(); i++) {
                        Map.Entry<ExecutionIndex, Integer> e = entryIterator.next();
                        // Only mutate `mutationSize` contiguous entries from
                        // the randomly selected `idx`.
                        if (i >= offset && i < (offset + mutationSize)) {
                            // Apply a random mutation
                            int mutatedValue = setToZero ? 0 : random.nextInt(256);
                            e.setValue(mutatedValue);
                        }
                    }
                }
            }

            return newInput;

        }

        public Iterator<Integer> iterator() {
            return new Iterator<Integer>() {

                Iterator<ExecutionIndex> keyIt = orderedKeys.iterator();

                @Override
                public boolean hasNext() {
                    return keyIt.hasNext();
                }

                @Override
                public Integer next() {
                    return valuesMap.get(keyIt.next());
                }
            };
        }
    }

    public static class SeedInput extends LinearInput {
        final Optional<File> seedFile;

        /**
         * WARNING This version assumes we saved the hints into the file...
         * @param seedFile
         * @throws IOException
         */
        public SeedInput(File seedFile) throws IOException {
            super();
            this.seedFile = Optional.of(seedFile);
            try(ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(new FileInputStream(seedFile)))){
                int inputSize = ois.readInt();
                byte[] input = new byte[inputSize];
                ois.readFully(input);
                LinkedList<int[]> instructions = (LinkedList<int[]>) ois.readObject();
                LinkedList<Coordinator.StringHint[]> stringHints = (LinkedList<Coordinator.StringHint[]>) ois.readObject();
                LinkedList<Coordinator.TargetedHint> targetedHints = (LinkedList<Coordinator.TargetedHint>) ois.readObject();
                this.offsetOfLastHintAdded = ois.readInt();
                this.allInstructions = (LinkedList<int[]>) ois.readObject();
                this.allStringEqualsHints = (LinkedList<Coordinator.StringHint[]>) ois.readObject();
                this.stringEqualsHints = stringHints;
                this.instructions = instructions;
                this.appliedTargetedHints = targetedHints;
                this.organizeStringHintsForCombinations();
                this.values = new ShortArrayList(input.length);
                for(int i = 0; i < input.length; i++){
                    this.values.add((short) (input[i] & 0xff));
                }

            } catch (ClassNotFoundException e) {
                e.printStackTrace();
            }
            //this.in = new BufferedInputStream(new FileInputStream(seedFile));
            this.desc = "seed";
        }

        /**
         * WARNING This version does NOT assume that the hints were packed in...
         * @param seedBytes
         * @param desc
         */
        public SeedInput(byte[] seedBytes, String desc) {
            this.seedFile = Optional.empty();
            this.desc = desc;
            this.values = new ShortArrayList(seedBytes.length);
            for(int i = 0; i < seedBytes.length; i++){
                this.values.add((short) (seedBytes[i] & 0xff));
            }
        }

    }


    static class InputLocation {
        private final MappedInput input;
        private final int offset;

        InputLocation(MappedInput input, int offset) {
            this.input = input;
            this.offset = offset;
        }
    }

    static class InputPrefixMapping {
        private final MappedInput sourceInput;
        private final Prefix sourcePrefix;
        private final Prefix targetPrefix;

        InputPrefixMapping(MappedInput sourceInput, Prefix sourcePrefix, Prefix targetPrefix) {
            this.sourceInput = sourceInput;
            this.sourcePrefix = sourcePrefix;
            this.targetPrefix = targetPrefix;
        }
    }

}
