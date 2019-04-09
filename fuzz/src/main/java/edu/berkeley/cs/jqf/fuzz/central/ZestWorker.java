package edu.berkeley.cs.jqf.fuzz.central;

import edu.berkeley.cs.jqf.fuzz.guidance.Result;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.LinkedList;

class ZestWorker extends Worker {
    private ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
    private ArrayList<Integer> fuzzing = new ArrayList<>();
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

                // Let central thread know
                int size = 0;
                for (byte[] b : inputRequests)
                    size += b.length;
                byte[] bs = new byte[size];
                int i = 0;
                for (byte[] b : inputRequests) {
                    System.arraycopy(b, 0, bs, i, bs.length);
                    i += bs.length;
                }

                c.foundInput(id, bs);
            } else if (o instanceof Integer) {
                // Select input
                int selected = (Integer)o;

                // Select part of the input to fuzz
                int i = 0;
                int offset = 0;
                int size = 0;
                int toFuzz = fuzzing.get(selected);
                LinkedList<int[]> instructionsToSend = new LinkedList<>();
                for (byte[] b : inputs.get(selected)) {
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
}
