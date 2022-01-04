package edu.berkeley.cs.jqf.fuzz.central;

import za.ac.sun.cs.green.service.z3.Z3JavaTranslator;

import java.io.*;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedList;
import java.util.Optional;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

/**
 * A shim to sit between central + Z3. Libz3java has some latent bugs that can cause the JVM to segfault.
 * Making the coordinator fault tolerant to segfaults is an unpleasant activity. But, at the same time, most calls into Z3
 * take seconds to get an answer to, and we do not store any shared state in Z3 to reuse between calls. So, now Z3 sits in a separate
 * process, invoked on demand, but this shim.
 */
public class RemoteZ3WorkerFacade {
    static final int MARGIN_FOR_SERIALIZATION = 5000; //Extra time to wait for process to finish

    private static void appendSystemPropertyIfDefined(String prop, LinkedList<String> list) {
        String s = System.getProperty(prop);
        if (s != null) {
            list.add("-D" + prop + "=" + s);
        }
    }

    static PrintWriter statsLogger;

    static {
        String z3StatsFile = System.getProperty("z3StatsLog");
        if (z3StatsFile != null) {
            try {
                statsLogger = new PrintWriter(new BufferedWriter(new FileWriter(z3StatsFile)));
                Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
                    @Override
                    public void run() {
                        if (statsLogger != null)
                            statsLogger.close();
                    }
                }));
                statsLogger.println("time,numBranchesUnsolved,selectedBranch,numInputsNotTried,selectedInput,timeSpent,result");
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    public static void appendToLogFile(int numBranchesUnsolved, String selectedBranch, int numInputsNotTried, int numInputsTried, int selectedInput, int timeSpent, String result) {

        if (statsLogger != null) {
            statsLogger.println(String.format("%d,%d,%s,%d,%d,%d,%d,%s",
                    System.currentTimeMillis(),
                    numBranchesUnsolved,
                    selectedBranch,
                    numInputsNotTried,
                    numInputsTried, selectedInput, timeSpent, result
            ));
            statsLogger.flush();
        }
    }

    public Optional<Coordinator.Input> exploreTarget(Z3Worker.Target target) throws TimeoutException {
        try {
            Path inputToZ3Worker = Files.createTempFile("knarr_z3_input", ".ser");
            Path outputFromZ3Worker = Files.createTempFile("knarr_z3_output", ".ser");

            ObjectOutputStream oos = new ObjectOutputStream(new BufferedOutputStream(new FileOutputStream(inputToZ3Worker.toFile())));
            oos.writeObject(target);
            oos.close();

            String separator = System.getProperty("file.separator");
            String classpath = System.getProperty("java.class.path");
            String path = System.getProperty("java.home")
                    + separator + "bin" + separator + "java";
            LinkedList<String> z3Args = new LinkedList<>();
            z3Args.add(path);
            z3Args.add("-cp");
            z3Args.add(classpath);
            z3Args.add("-Xmx1g");
            z3Args.add("-Xss16m");
            appendSystemPropertyIfDefined("java.library.path", z3Args);
            appendSystemPropertyIfDefined("Z3_timeout", z3Args);
            z3Args.add("edu.berkeley.cs.jqf.fuzz.central.Z3Worker");
            z3Args.add(inputToZ3Worker.toAbsolutePath().toString());
            z3Args.add(outputFromZ3Worker.toAbsolutePath().toString());
            ProcessBuilder pb = new ProcessBuilder(z3Args);

            pb = pb.inheritIO();
            Process proc = pb.start();

            try {
                try {
                    proc.waitFor(Z3JavaTranslator.timeoutMS + MARGIN_FOR_SERIALIZATION, TimeUnit.MILLISECONDS);
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
                if (proc.isAlive()) {
                    long pid = getPidOfProcess(proc);
                    if (pid > 0) {
                        Runtime.getRuntime().exec(new String[]{"kill", "-9", "" + pid});
                    }
                    throw new TimeoutException("Z3 Process didn't finish in time");
                }
                if (proc.exitValue() != 0) {
                    throw new TimeoutException("Non-zero exit from Z3");
                }

                //Check for output
                if (Files.size(outputFromZ3Worker) == 0) {
                    throw new TimeoutException("Empty output from Z3, see Z3 process output for details, likely timeout");
                }

                ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(new FileInputStream(outputFromZ3Worker.toFile())));
                Coordinator.Input ret = null;
                if (ois.readBoolean()) {
                    ret = (Coordinator.Input) ois.readObject();
                }
                ois.close();
                if (ret != null) {
                    return Optional.of(ret);
                } else {
                    return Optional.empty();
                }
            }
            finally{
                Files.deleteIfExists(inputToZ3Worker);
                Files.deleteIfExists(outputFromZ3Worker);
            }
        } catch (IOException | ClassNotFoundException e) {
            e.printStackTrace();
        }
        return Optional.empty();
    }

    public static long getPidOfProcess(Process p) {
        long pid = -1;

        try {
            if (p.getClass().getName().equals("java.lang.UNIXProcess")) {
                Field f = p.getClass().getDeclaredField("pid");
                f.setAccessible(true);
                pid = f.getLong(p);
                f.setAccessible(false);
            }
        } catch (Exception e) {
            pid = -1;
        }
        return pid;
    }
}
