package edu.berkeley.cs.jqf.fuzz.random;

import edu.berkeley.cs.jqf.fuzz.guidance.Result;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.nio.ByteBuffer;
import java.util.LinkedList;
import java.util.Random;

public class Central {

    public static void main(String[] args) throws IOException, ClassNotFoundException {
        ServerSocket ss = new ServerSocket(54321);

        Socket s = ss.accept();

        ObjectOutputStream oos = new ObjectOutputStream(s.getOutputStream());
        ObjectInputStream  ois = new ObjectInputStream(s.getInputStream());

        // Get initial valid value
        LinkedList<byte[]> values = new LinkedList<>();
        Result res = Result.INVALID;
        while (res == Result.INVALID) {
            oos.writeObject(new LinkedList<byte[]>());
            oos.writeInt(100);
            oos.flush();
            values = (LinkedList<byte[]>) ois.readObject();
            res = (Result) ois.readObject();
        }

        for (byte[] a : values) {
            ByteBuffer bf = ByteBuffer.wrap(a);
            switch (a.length) {
                case 4:
                    System.out.println("\t" + bf.getInt());
                    break;
                case 2:
                    System.out.println("\t" + bf.getShort());
                    break;
                default:
                    System.out.println("\t" + new String(a));
            }
        }
        System.out.println(res);

        Random rnd = new Random();

        while (true) {
            int toMutate = rnd.nextInt(values.size());
            System.out.println(toMutate);

            LinkedList mutating = new LinkedList(values);
            mutating.set(toMutate, new byte[0]);

            out: for (int i = 0 ; i < 1 ; i++) {
                oos.writeObject(new LinkedList(mutating));
                oos.writeInt(1000);
                oos.flush();
                LinkedList<byte[]> read = (LinkedList<byte[]>) ois.readObject();
                res = (Result) ois.readObject();
                switch (res) {
                    case INVALID:
                        break;
                    case SUCCESS:
                        break;
                    case FAILURE:
                        System.out.println(res);
                        System.out.println(i);
                        for (byte[] a : read) {
                            ByteBuffer bf = ByteBuffer.wrap(a);
                            switch (a.length) {
                                case 4:
                                    System.out.println("\t" + bf.getInt());
                                    break;
                                case 2:
                                    System.out.println("\t" + bf.getShort());
                                    break;
                                case 1:
                                    System.out.println("\t" + Boolean.toString(a[0] == 0));
                                    break;
                                default:
                                    System.out.println("\t" + new String(a));
                            }
                        }
                        break;
                    default:
                        System.out.println(res);
                        break;
                }
//                System.out.println("\t" + read.get(toMutate));
            }
        }
    }
}
