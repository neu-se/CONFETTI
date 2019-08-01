package edu.berkeley.cs.jqf.fuzz.central;

import edu.berkeley.cs.jqf.fuzz.guidance.Result;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.TreeSet;

class ZestWorker extends Worker {
    private ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
    private ArrayList<Integer> fuzzing = new ArrayList<>();
    private ArrayList<TreeSet<Integer>> recommendations = new ArrayList<>();
    private ArrayList<HashMap<Integer, HashSet<String>>> stringEqualsHints = new ArrayList<>();
    private ArrayList<HashMap<Integer, HashSet<String>>> indexOfHints = new ArrayList<>();
    private Coordinator c;

    private final String[] EMPTY = new String[0];

    public ZestWorker(ObjectInputStream ois, ObjectOutputStream oos, Coordinator c) throws IOException {
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

                LinkedList<String[]> hints = (LinkedList<String[]>) ois.readObject();

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

                c.foundInput(id, bs, res != Result.INVALID, hints);

                synchronized (recommendations) {
                    recommendations.add(new TreeSet<>());
                    stringEqualsHints.add(null);
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
                LinkedList<String[]> stringsToSend = new LinkedList<>();
                TreeSet<Integer> recs;
                synchronized (recommendations) {
                    recs = recommendations.get(selected);
                }

                HashMap<Integer, HashSet<String>> inputStrings = stringEqualsHints.get(selected);

                for (byte[] b : inputs.get(selected)) {
                    if (!recs.isEmpty()) {
                        boolean addThis = false;

                        for (int j = offset ; j < offset+b.length ; j++) {
                            addThis =recs.contains(j);

                            if (addThis)
                                break;
                        }

                        if (!addThis) {
                            offset += b.length;
                            continue;
                        }

                        instructionsToSend.addLast(new int[]{offset, b.length});
                        if (inputStrings != null && inputStrings.containsKey(offset))
                            stringsToSend.addLast(inputStrings.get(offset).toArray(new String[0]));
                        else
                            stringsToSend.addLast(EMPTY);
                    }

                    offset += b.length;
                }

                // Send instructions
                oos.writeObject(instructionsToSend);
                oos.writeObject(stringsToSend);
                oos.reset();

                printSentStringHints(stringsToSend);

                // Update state
                fuzzing.set(selected, (toFuzz + 1) % inputs.get(selected).size());
            }
        }
    }

    private void printSentStringHints(LinkedList<String[]> stringHintsSent) {
        if (stringHintsSent.isEmpty())
            return;

        System.out.print("\tSent strings: ");
        for (String[] s : stringHintsSent) {
            if (s.length == 0)
                continue;

            System.out.print("[ ");
            for (String ss : s)
                System.out.print(ss + ",");
            System.out.print("] ");
        }

        System.out.println();
    }

    public void recommend(int inputID, TreeSet<Integer> recommendation, HashMap<Integer, HashSet<String>> eqs,HashMap<Integer, HashSet<String>> ios ) {
        synchronized (recommendations) {
            recommendations.set(inputID, recommendation);
            stringEqualsHints.set(inputID, eqs);
            //indexOfHints.set(inputID, ios);
        }
    }
}
