package edu.berkeley.cs.jqf.fuzz.central;

import java.io.*;
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
        ois = new ObjectInputStream(s.getInputStream());
        oos = new ObjectOutputStream(new BufferedOutputStream(s.getOutputStream()));
    }

    protected enum Type { Zest_Initial, Zest, Knarr };

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
        System.out.println(args.length);
        if (args.length > 0) {
            try (FileInputStream fis = new FileInputStream(args[0])) {
                props.load(fis);
                System.out.println(props);
            }
        }
        Coordinator.Config config  = new Coordinator.Config(props);
        Coordinator c = new Coordinator(config);

        new Thread(c, "CONFETTI Coordinator").start();

        while (true) {
            Socket s = ss.accept();

            ObjectOutputStream oos = new ObjectOutputStream(s.getOutputStream());
            ObjectInputStream ois = new ObjectInputStream(s.getInputStream());

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
                        new Thread(zest, "CONFETTI Zest Worker").start();
                    }
                    break;
                default:
                    throw new Error("Unknown type");
            }
        }
    }

}
