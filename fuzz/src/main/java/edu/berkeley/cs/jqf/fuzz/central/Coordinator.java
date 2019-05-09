package edu.berkeley.cs.jqf.fuzz.central;

import java.io.IOException;
import java.io.Serializable;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Objects;
import java.util.Properties;
import java.util.TreeSet;

public class Coordinator implements Runnable {
    private LinkedList<Input> inputs = new LinkedList<>();
    private HashMap<Branch, Branch> branches = new HashMap<>();
    private HashMap<Input, HashSet<String>> perInputStringEqualsHints = new HashMap<>();
    private HashMap<Input, HashMap<Integer, HashSet<String>>> perByteStringEqualsHints = new HashMap<>();
    private HashSet<String> globalStringEqualsHints = new HashSet<>();
    private KnarrWorker knarr;
    private ZestWorker zest;

    private final Config config;

    public Coordinator(Config config) {
        this.config = config;
    }

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

            int n = 0;
            for (Input input : m) {
                if (input.isNew) {
                    if (n++ > 10)
                        break;
                    // Compute coverage and branches with Knarr
                    LinkedList<Branch> bs;
                    HashMap<Integer, HashSet<String>> eqs = new HashMap<>();
                    try {
                        bs = knarr.getBranchCoverage(input.bytes, eqs);
                        if (!eqs.isEmpty()) {
                            switch (config.hinting) {
                                case NONE:
                                    break;
                                case GLOBAL:
                                    for (HashSet<String> s : eqs.values())
                                        globalStringEqualsHints.addAll(s);
                                    break;
                                case PER_INPUT:
                                    HashSet<String> ss = new HashSet<>();
                                    for (HashSet<String> s : eqs.values())
                                        ss.addAll(s);
                                    perInputStringEqualsHints.put(input, ss);
                                    break;
                                case PER_BYTE:
                                    perByteStringEqualsHints.put(input, eqs);
                                    break;
                                default:
                                    throw new Error("Not implemented");
                            }

                        }
                    } catch (IOException e) {
                        throw new Error(e);
                    }

                    // Check if any previous branches were explored
                    branches: for (Branch b : bs) {
                        if (b.source == null)
                            continue;

                        for (String f : config.filter)
                            if (b.source.contains(f))
                                continue branches;

                        Branch existing;
                        if (!branches.containsKey(b)) {
                            existing = b;
                            existing.trueExplored = new HashSet<>();
                            existing.falseExplored = new HashSet<>();
                            existing.control = new HashMap<>();
                            existing.keep = b.keep;
                            existing.source = (b.source == null ? "" : b.source);
                            branches.put(b, b);
                        } else {
                            existing = branches.get(b);
                        }

                        if (b.result) {
                            if (existing.trueExplored.isEmpty())
                                System.out.println("\tInput " + input.id + " explores T on " + existing.takenID + " (" + existing.source + ")");
                            existing.trueExplored.add(input);
                        } else {
                            if (existing.falseExplored.isEmpty())
                                System.out.println("\tInput " + input.id + " explores F on " + existing.takenID + " (" + existing.source + ")");
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

                    HashMap<Integer, HashSet<String>> stringHints = new HashMap<>();
                    switch (config.hinting) {
                        case NONE:
                            break;
                        case GLOBAL:
                            HashSet<String> globals = new HashSet<>(globalStringEqualsHints);
                            for (int i = 0 ; i < input.bytes.length ; i++)
                                stringHints.put(i, globals);
                            break;
                        case PER_INPUT:
                            HashSet<String> perInput = new HashSet<>(perInputStringEqualsHints.getOrDefault(input, new HashSet<>()));
                            for (int i = 0 ; i < input.bytes.length ; i++)
                                stringHints.put(i, perInput);
                            break;
                        case PER_BYTE:
                            stringHints.putAll(perByteStringEqualsHints.getOrDefault(input, new HashMap<>()));
                            break;
                        default:
                            throw new Error("Not implemented");
                    }

                    zest.recommend(input.id, recommendation, stringHints);
                }
            }
        }
    }

    public final synchronized  void setKnarrWorker(KnarrWorker knarr, ZestWorker zest) {
        this.knarr = knarr;
        this.zest = zest;
        this.notifyAll();
    }

    public Config getConfig() {
        return this.config;
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
        public String source = "";

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

    public static class Config {
        public enum Hinting { NONE, GLOBAL, PER_INPUT, PER_BYTE }

        public final String[] filter;
        public final Hinting hinting;

        public Config(Properties p) {
            {
                String f = p.getProperty("path.filter");
                filter = (f == null) ? null : f.split(",");
            }
            {
                Hinting h;
                try {
                    h = Hinting.valueOf(p.getProperty("string.hints"));
                } catch (IllegalArgumentException _) {
                    h = Hinting.NONE;
                }

                hinting = h;
            }
        }
    }
}
