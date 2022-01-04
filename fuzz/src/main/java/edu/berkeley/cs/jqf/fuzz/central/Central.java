package edu.berkeley.cs.jqf.fuzz.central;

import java.io.*;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryMXBean;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Properties;

public class Central {
    private static final int PORT = Integer.getInteger("centralPort",54321);

    protected Socket s;
    protected ObjectInputStream ois;
    protected ObjectOutputStream oos;

    protected Central() throws IOException {
        this.s = new Socket(InetAddress.getLocalHost(), PORT);
        s.setTcpNoDelay(true);
        oos = new ObjectOutputStream(new BufferedOutputStream(s.getOutputStream()));
        ois = new ObjectInputStream(new BufferedInputStream(s.getInputStream()));
    }

    protected enum Type { Zest_Initial, Zest, Knarr };
    static boolean PROFILE_HEAP_USAGE = Boolean.valueOf(System.getenv("PROFILE_HEAP") != null ? System.getenv("PROFILE_HEAP") : "false");

    /* Server:
     * 1. Receive input
     * 2. Receive coverage
     * 3. Receive selected input
     * 3. Send instructions
     */
    public static void main(String[] args) throws Throwable {

       // System.load("/home/jamesk/Documents/jqf-artifact/software/knarr/z3-4.6.0-x64-ubuntu-16.04/bin/libz3java.so");
        ServerSocket ss = new ServerSocket(PORT);

        ZestWorker zest = null;
        KnarrWorker knarr = null;

        Properties props = new Properties();
        String outputDirectoryName = args.length > 0 ? args[0] : "fuzz-results";
        File outputDirectory = new File(outputDirectoryName);
        if(!outputDirectory.exists()){
            outputDirectory.mkdirs();
        }
        if (args.length > 1) {
            try (FileInputStream fis = new FileInputStream(args[1])) {
                props.load(fis);
                System.out.println(props);
            }
        }
        Coordinator.Config config  = new Coordinator.Config(props);
        Coordinator c = new Coordinator(config);

        if(PROFILE_HEAP_USAGE){
            //Set up a thread to dump heap usage every ZEST_STATS_REFRESH_TIME_PERIOD millisec
            try {
                final PrintWriter pw = new PrintWriter(new FileWriter(new File(outputDirectory, "confetti-central-memory.csv")));
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

        new Thread(c, "CONFETTI Coordinator").start();

        while (true) {
            Socket s = ss.accept();

            ObjectOutputStream oos = new ObjectOutputStream(new BufferedOutputStream(s.getOutputStream()));
            oos.flush();
            ObjectInputStream ois = new ObjectInputStream(new BufferedInputStream(s.getInputStream()));

            Type t = (Type) ois.readObject();
            switch (t) {

                case Knarr:
                    if (knarr != null) {
                        s.close();
                    } else {
                        knarr = new KnarrWorker(ois, oos, c);
                        c.setKnarrWorker(knarr, zest);
                    }
                    break;
                case Zest_Initial:
                    if (zest != null) {
                        s.close();
                    }
                    else {
                        if (config.triggerZ3) {
                            oos.writeObject(config.triggerZ3SampleWindow);
                            oos.writeObject(config.triggerZ3SampleThreshold);
                            oos.flush();

                        } else {
                            oos.writeObject(null);
                            oos.writeObject(null);
                            oos.flush();
                        }

                        zest = new ZestWorker(ois, oos, c);
                        if(knarr != null && c.zest == null){
                            c.zest = zest;
                        }
                        new Thread(zest, "CONFETTI Zest Worker").start();
                    }
                    break;
                default:
                    throw new Error("Unknown type");
            }
        }
    }

}
