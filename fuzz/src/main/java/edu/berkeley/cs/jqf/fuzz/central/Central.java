package edu.berkeley.cs.jqf.fuzz.central;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
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
        Socket s = new Socket(InetAddress.getLocalHost(), PORT);
        ois = new ObjectInputStream(s.getInputStream());
        oos = new ObjectOutputStream(s.getOutputStream());
    }

    protected enum Type { Zest, Knarr };

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

        Coordinator c = new Coordinator(new Coordinator.Config(props));

        new Thread(c).start();

        while (true) {
            Socket s = ss.accept();

            ObjectOutputStream oos = new ObjectOutputStream(s.getOutputStream());
            ObjectInputStream ois = new ObjectInputStream(s.getInputStream());

            Type t = (Type) ois.readObject();

            switch (t) {
                case Zest:
                    if (zest != null) {
                        s.close();
                    } else {
                        zest = new ZestWorker(ois, oos, c);
                        new Thread(zest).start();
                    }
                    break;
                case Knarr:
                    if (knarr != null) {
                        s.close();
                    } else {
                        knarr = new KnarrWorker(ois, oos, c);
                        c.setKnarrWorker(knarr, zest);
                    }
                    break;
                default:
                    throw new Error("Unknown type");
            }
        }
    }

}
