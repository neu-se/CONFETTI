package edu.berkeley.cs.jqf.fuzz.central;

import edu.berkeley.cs.jqf.fuzz.guidance.Result;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.TreeSet;

class ZestWorker extends Worker {
    private ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
    private ArrayList<Integer> fuzzing = new ArrayList<>();
    private ArrayList<TreeSet<Integer>> recommendations = new ArrayList<>();
    private Coordinator c;

    public ZestWorker(ObjectInputStream ois, ObjectOutputStream oos, Coordinator c) {
        super(ois, oos);
        this.c = c;
    }

    @Override
    public void work() throws IOException, ClassNotFoundException {

        while (true) {
            // Receive input or select new input
            Object o = ois.readObject();

            if (o instanceof LinkedList) {
                // Receive input
                LinkedList<byte[]> inputRequests = (LinkedList<byte[]>) o;
                Result res = (Result) ois.readObject();
                int id = ois.readInt();

                // Receive coverage
//                Coverage cov = (Coverage) ois.readObject();

                // Save input
                inputs.add(id, inputRequests);
                fuzzing.add(id, 0);

                // Let coordinator thread know
                int size = 0;
                for (byte[] b : inputRequests)
                    size += b.length;
                byte[] bs = new byte[size];
                int i = 0;
                for (byte[] b : inputRequests) {
                    System.arraycopy(b, 0, bs, i, b.length);
                    i += b.length;
                }

                c.foundInput(id, bs);

                synchronized (recommendations) {
                    recommendations.add(new TreeSet<>());
                }

            } else if (o instanceof Integer) {
                // Select input
                int selected = (Integer)o;

                // Select part of the input to fuzz
                int i = 0;
                int offset = 0;
                int size = 0;
                int toFuzz = fuzzing.get(selected);
                LinkedList<int[]> instructionsToSend = new LinkedList<>();
                TreeSet<Integer> recs;
                synchronized (recommendations) {
                    recs = recommendations.get(selected);
                }

                for (byte[] b : inputs.get(selected)) {
                    if (!recs.isEmpty()) {
                        boolean addThis = false;

                        for (int j = offset ; j < offset+b.length ; j++) {
                            if (recs.contains(j)) {
                                addThis = true;
                                break;
                            }
                        }

                        if (!addThis)
                            continue;
                    }

                    instructionsToSend.addLast(new int[]{offset, b.length});
                    offset += b.length;
                }

                // Send instructions
                oos.writeObject(instructionsToSend);

                // Update state
                fuzzing.set(selected, (toFuzz + 1) % inputs.get(selected).size());
            }
        }
    }

    public void recommend(int inputID, TreeSet<Integer> recommendation) {
        synchronized (recommendations) {
            recommendations.set(inputID, recommendation);
        }
    }
}
