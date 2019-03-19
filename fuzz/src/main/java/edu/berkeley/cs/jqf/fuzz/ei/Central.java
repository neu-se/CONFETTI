package edu.berkeley.cs.jqf.fuzz.ei;

import com.pholser.junit.quickcheck.random.SourceOfRandomness;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.LinkedList;
import java.util.Random;

public class Central {

    public static void main(String[] args) throws IOException, ClassNotFoundException {
        ServerSocket ss = new ServerSocket(54321);

        Socket s = ss.accept();

        ObjectOutputStream oos = new ObjectOutputStream(s.getOutputStream());
        ObjectInputStream  ois = new ObjectInputStream(s.getInputStream());

        Random rnd = new Random();
        oos.writeObject(new TrackingRandomness(rnd));

        TrackingRandomness r = (TrackingRandomness) ois.readObject();

        LinkedList values = r.requests;

        System.out.println(values);

        while (true) {
            int toMutate = rnd.nextInt(values.size());
            System.out.println(toMutate);

            LinkedList mutating = new LinkedList(values);
            mutating.set(toMutate, new Object());

            for (int i = 0 ; i < 1000 ; i++) {
                oos.writeObject(new PartiallyFixedRandom(rnd, mutating));
                ois.readObject();
            }
        }

    }

    public static class TrackingRandomness extends SourceOfRandomness implements Serializable {
        private LinkedList requests = new LinkedList();

        public TrackingRandomness(Random delegate) {
            super(delegate);
        }

        @Override
        public boolean nextBoolean() {
            boolean ret = super.nextBoolean();
            requests.addLast(ret);
            return ret;
        }

        @Override
        public int nextInt(int n) {
            int ret = super.nextInt(n);
            requests.addLast(ret);
            return ret;
        }

        @Override
        public <T> T choose(T[] items) {
            int ret = super.nextInt(items.length);
            requests.addLast(ret);
            return items[ret];
        }
    }

    public static class PartiallyFixedRandom extends SourceOfRandomness implements Serializable {
        private LinkedList outputs;

        public PartiallyFixedRandom(Random delegate, LinkedList outputs) {
            super(delegate);
            this.outputs = outputs;
        }

        @Override
        public boolean nextBoolean() {
            Object next = outputs.removeFirst();

            if (next instanceof Boolean)
                return (Boolean)next;

            return super.nextBoolean();
        }

        @Override
        public int nextInt(int n) {
            Object next = outputs.removeFirst();

            if (next instanceof Integer)
                return (Integer)next;

            return super.nextInt(n);
        }

        @Override
        public <T> T choose(T[] items) {
            Object next = outputs.removeFirst();

            if (next instanceof Integer)
                return items[(Integer)next];

            return super.choose(items);
        }
    }
}
