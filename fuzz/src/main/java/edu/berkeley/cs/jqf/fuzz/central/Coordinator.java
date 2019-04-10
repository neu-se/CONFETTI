package edu.berkeley.cs.jqf.fuzz.central;

import java.io.IOException;
import java.io.Serializable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Objects;

public class Coordinator implements Runnable {
    private LinkedList<Input> inputs = new LinkedList<>();
    private HashMap<Branch, Branch> branches = new HashMap<>();
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
            LinkedList<Input> m;

            synchronized (this) {
                boolean newInputs = false;

                if (this.knarr != null)
                    for (Input i : inputs) {
                        if (i.isNew) {
                            newInputs = true;
                            break;
                        }
                    }

                if (!newInputs) {
                    try {
                        this.wait();
                        continue;
                    } catch (InterruptedException e) {
                        continue;
                    }
                }

                m = new LinkedList<>(inputs);
            }

            for (Input input : m) {
                if (input.isNew) {
                    // Compute coverage and branches with Knarr
                    LinkedList<Branch> bs;
                    try {
                        bs = knarr.getBranchCoverage(input.bytes);
                    } catch (IOException e) {
                        throw new Error(e);
                    }

                    // Check if any previous branches were explored
                    for (Branch b : bs) {
                        Branch existing;
                        if (!branches.containsKey(b)) {
                            branches.put(b, b);
                            existing = b;
                            b.trueExplored = new HashSet<>();
                            b.falseExplored = new HashSet<>();
                        } else {
                            existing = branches.get(b);
                        }

                        if (b.result) {
                            if (existing.trueExplored.isEmpty())
                                System.out.println("\tInput " + input.id + " explores T on " + existing.takenID);
                            existing.trueExplored.add(input);
                        } else {
                            if (existing.falseExplored.isEmpty())
                                System.out.println("\tInput " + input.id + " explores F on " + existing.takenID);
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
        boolean isNew;
    }

    public static class Branch implements Serializable {
        public int takenID, notTakenID;
        public boolean result;

        transient HashSet<Input> trueExplored;
        transient HashSet<Input> falseExplored;

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Branch branch = (Branch) o;
            return takenID == branch.takenID &&
                    notTakenID == branch.notTakenID;
        }

        @Override
        public int hashCode() {
            return Objects.hash(takenID, notTakenID);
        }
    }
}
