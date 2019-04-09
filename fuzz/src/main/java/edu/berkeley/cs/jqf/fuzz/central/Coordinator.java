package edu.berkeley.cs.jqf.fuzz.central;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

class Coordinator implements Runnable {
    private LinkedList<Input> inputs = new LinkedList<>();
    private HashMap<Long, Branch> branches = new HashMap<>();
    private KnarrWorker knarr;

    protected final synchronized void foundInput(int id, byte[] bytes) {
        Input in = new Input();
        in.bytes = bytes;
        in.id = id;
        in.isNew = true;
        this.inputs.addLast(in);
        this.notifyAll();

        System.out.println("Input added " + id);
    }

    @Override
    public void run() {

        while (true) {
            List<Input> m;

            synchronized (this) {
                try {
                    this.wait();
                } catch (InterruptedException e) {
                    // Nothing
                }

                if (this.knarr == null)
                    continue;

                m = Collections.unmodifiableList(inputs);
            }

            for (Input input : m) {
                if (input.isNew) {
                    // Compute coverage and branches with Knarr
                    input.branches = knarr.getBranchCoverage(input.bytes);

                    // Check if any previous branches were explored
                    for (Branch b : input.branches) {
                        Branch existing;
                        if (!branches.containsKey(b.id)) {
                            branches.put(b.id, b);
                            existing = b;
                        } else {
                            existing = branches.get(b.id);
                        }

                        if (b.result) {
                            if (existing.trueExplored.isEmpty())
                                System.out.println("\tInput " + input.id + " explores T on " + existing.id);
                            existing.trueExplored.add(input);
                        } else {
                            if (existing.falseExplored.isEmpty())
                                System.out.println("\tInput " + input.id + " explores F on " + existing.id);
                            existing.falseExplored.add(input);
                        }
                    }

                    input.isNew = false;
                }
            }
        }
    }

    public final synchronized  void setKnarrWorker(KnarrWorker knarr) {
        this.knarr = knarr;
        this.notifyAll();
    }

    private static class Input {
        int id;
        byte[] bytes;
        HashSet<Branch> branches;
        boolean isNew;
    }

    public static class Branch {
        long id;
        LinkedList<Integer> bytesControlling;
        boolean result;

        HashSet<Input> trueExplored = new HashSet<>();
        HashSet<Input> falseExplored = new HashSet<>();
    }
}
