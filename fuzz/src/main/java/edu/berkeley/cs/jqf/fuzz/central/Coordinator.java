package edu.berkeley.cs.jqf.fuzz.central;

import java.io.IOException;
import java.io.Serializable;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Objects;
import java.util.TreeSet;

public class Coordinator implements Runnable {
    private LinkedList<Input> inputs = new LinkedList<>();
    private HashMap<Branch, Branch> branches = new HashMap<>();
    private KnarrWorker knarr;
    private ZestWorker zest;

    protected final synchronized void foundInput(int id, byte[] bytes, boolean valid) {
        Input in = new Input();
        in.bytes = bytes;
        in.id = id;
        in.isNew = valid;
        this.inputs.addLast(in);
        this.notifyAll();

        System.out.println("Input added " + id);
    }

    @Override
    public void run() {

        HashMap<Integer, TreeSet<Integer>> lastRecommendation = new HashMap<>();

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
                            existing = b;
                            existing.trueExplored = new HashSet<>();
                            existing.falseExplored = new HashSet<>();
                            existing.control = new HashMap<>();
                            existing.keep = b.keep;
                            branches.put(b, b);
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

                        LinkedList<Integer> bytes = new LinkedList<>(b.controllingBytes);
                        Collections.sort(bytes);

                        existing.control.put(input, bytes.toArray(new Integer[0]));
                    }

                    input.isNew = false;
                }
            }

            // Make recommendations
            synchronized (this) {
                for (Input input : inputs) {
                    TreeSet<Integer> recommendation = new TreeSet<>();
                    for (Branch branch : branches.values()) {
                        if (branch.falseExplored.isEmpty() || branch.trueExplored.isEmpty() || branch.keep) {
                            if (branch.control.containsKey(input)) {
                                for (int i : branch.control.get(input))
                                    recommendation.add(i);
                            }
                        }
                    }

                    if (!lastRecommendation.containsKey(input.id) || !recommendation.equals(lastRecommendation.get(input.id))) {
                        System.out.println(input.id + " -> " + recommendation);
                        lastRecommendation.put(input.id, recommendation);
                    }

                    zest.recommend(input.id, recommendation);
                }
            }
        }
    }

    public final synchronized  void setKnarrWorker(KnarrWorker knarr, ZestWorker zest) {
        this.knarr = knarr;
        this.zest = zest;
        this.notifyAll();
    }

    private static class Input {
        int id;
        byte[] bytes;
        boolean isNew;

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Input input = (Input) o;
            return id == input.id;
        }

        @Override
        public int hashCode() {
            return Objects.hash(id);
        }
    }

    public static class Branch implements Serializable {
        public int takenID, notTakenID;
        public boolean result, keep;
        public HashSet<Integer> controllingBytes;

        transient HashMap<Input, Integer[]> control;
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
