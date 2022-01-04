package edu.berkeley.cs.jqf.fuzz.knarr;

import edu.berkeley.cs.jqf.fuzz.junit.GuidedFuzzing;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryMXBean;

public class KnarrDriver {
    static boolean PROFILE_HEAP_USAGE = Boolean.valueOf(System.getenv("PROFILE_HEAP") != null ? System.getenv("PROFILE_HEAP") : "false");

    public static void main(String[] args) {
        if (args.length < 2){
            System.err.println("Usage: java " + KnarrDriver.class + " TEST_CLASS TEST_METHOD");
            System.exit(1);
        }

        String testClassName  = args[0];
        String testMethodName = args[1];
        String outputDirectoryName = args.length > 2 ? args[2] : "fuzz-results";
        File outputDirectory = new File(outputDirectoryName);
        if(PROFILE_HEAP_USAGE){
            //Set up a thread to dump heap usage every ZEST_STATS_REFRESH_TIME_PERIOD millisec
            try {
                final PrintWriter pw = new PrintWriter(new FileWriter(new File(outputDirectory, "knarr-memory.csv")));
                Thread statsThread = new Thread(new Runnable() {
                    @Override
                    public void run() {
                        int waitTime = Integer.getInteger("ZEST_STATS_REFRESH_TIME_PERIOD", 300);
                        MemoryMXBean memoryMXBean = ManagementFactory.getMemoryMXBean();
                        pw.println("# unix_time,heapUsageBytes,nonHeapUsageBytes");
                        while (PROFILE_HEAP_USAGE) {
                            try {
                                Thread.sleep(waitTime);
                            } catch (InterruptedException e) {
                                e.printStackTrace();
                            }
                            if (PROFILE_HEAP_USAGE) {
                                pw.println(String.format("%s,%d,%d",System.currentTimeMillis(), memoryMXBean.getHeapMemoryUsage().getUsed(), memoryMXBean.getNonHeapMemoryUsage().getUsed()));
                            }
                        }
                    }
                }, "Memory Profile Logger");
                Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
                    @Override
                    public void run() {
                        PROFILE_HEAP_USAGE = false;
                        pw.flush();
                        pw.close();
                    }
                }));
                statsThread.setDaemon(true);
                statsThread.start();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        try {
            // Load the guidance
            String title = testClassName+"#"+testMethodName;
            KnarrGuidance guidance = new KnarrGuidance();

            // Run the Junit test
            GuidedFuzzing.run(testClassName, testMethodName, guidance, System.out);

        } catch (Exception e) {
            e.printStackTrace();
            System.exit(2);
        }

    }
}
