package edu.berkeley.cs.jqf.fuzz.central;

import org.jgrapht.alg.util.Pair;
import za.ac.sun.cs.green.expr.Expression;

import java.io.IOException;
import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

public class Coordinator implements Runnable {
    private LinkedList<Input> inputs = new LinkedList<>();
    private HashMap<Branch, Branch> branches = new HashMap<>();
    private HashMap<Input, HashSet<String>> perInputStringEqualsHints = new HashMap<>();
    private HashMap<Input, HashMap<Integer, HashSet<String>>> perByteStringEqualsHints = new HashMap<>();
    private HashSet<String> globalStringEqualsHints = new HashSet<>();



    private HashMap<Input, LinkedList<Expression>> constraints = new HashMap<>();
    private KnarrWorker knarr;
    private Z3Worker z3;
    private ZestWorker zest;

    private final Config config;

    public Coordinator(Config config) {
        this.config = config;
    }

    protected final synchronized void foundInput(int id, byte[] bytes, boolean valid, LinkedList<String[]>hints) {
        Input in = new Input();
        in.bytes = bytes;
        in.id = id;
        in.isNew = (config.useInvalid ? true : valid);
        in.hints = hints;

        this.inputs.addLast(in);
        //this.inputs.addFirst(in);
        this.notifyAll();

        System.out.println("Input added " + id);
        if(!hints.isEmpty())
            System.out.println("HINTS FOUND! " + hints);
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
                    // Get constraints from Knarr
                    LinkedList<Expression> cs;
                    try {
                        cs = knarr.getConstraints(input.bytes, input.hints);
                    } catch (IOException e) {
                        throw new Error(e);
                    }

                    this.constraints.put(input, cs);

                    // Compute coverage and branches from constraints
                    LinkedList<Branch> bs = new LinkedList<>();
                    HashMap<Integer, HashSet<String>> eqs = new HashMap<>();
                    for (Expression e : cs)
                        knarr.process(bs, eqs, e);

                    // Adjust string hints
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


                    {
                        ListIterator<Branch> iter = bs.listIterator(0);
                        while (iter.hasNext()) {
                            Branch b = iter.next();

                            for (String f : config.filter) {
                                if (b.source != null && b.source.contains(f)) {
                                    iter.remove();
                                    break;
                                }
                            }
                        }
                    }

                    // Check if any previous branches were explored
                    branches: for (Branch b : bs) {
                        if (b.source == null || b.controllingBytes.isEmpty())
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
                    targetZ3(null, null);
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

                    HashMap<Integer, HashSet<String>> stringEqualsHints = new HashMap<>();
                    switch (config.hinting) {
                        case NONE:
                            break;
                        case GLOBAL:
                            recommendation.clear();
                            HashSet<String> globals = new HashSet<>(globalStringEqualsHints);
                            for (int i = 0 ; i < input.bytes.length ; i++) {
                                stringEqualsHints.put(i, globals);
                            }
                            break;
                        case PER_INPUT:
                            recommendation.clear();
                            HashSet<String> perInput = new HashSet<>(perInputStringEqualsHints.getOrDefault(input, new HashSet<>()));
                            for (int i = 0 ; i < input.bytes.length ; i++) {
                                stringEqualsHints.put(i, perInput);
                            }
                            break;
                        case PER_BYTE:
                            stringEqualsHints.putAll(perByteStringEqualsHints.getOrDefault(input, new HashMap<>()));
                            break;
                        default:
                            throw new Error("Not implemented");
                    }

                    zest.recommend(input.id, recommendation, stringEqualsHints);
                }
            }
        }
    }

    private void targetZ3(Coordinator.Branch done, Optional<Pair<byte[], HashMap<Integer, HashSet<String>>>> result) {
        if (done != null) {
            System.out.println("Looks like Z3 found an input for this branch");
            throw new Error("Not implemented yet");
        }

        // Figure out what is the branch that needs the most attention
        Object[] tops = (Object[]) (branches.values().stream()
                .filter(b -> b.source != null)
                .filter(b -> b.falseExplored.isEmpty() || b.trueExplored.isEmpty())
                .sorted((b1,b2) -> Integer.compare(b2.trueExplored.size() + b2.falseExplored.size(), b1.trueExplored.size() + b1.falseExplored.size()))
                .limit(1)
                .toArray());

        Branch top;
        if (tops.length > 0)
            top = (Branch) tops[0];
        else
            return;

        // Create Z3 target
        List<Z3Worker.Target> targets = inputs.stream()
                .filter(i -> top.trueExplored.contains(i) || top.falseExplored.contains(i))
                .map(i -> new Z3Worker.Target(top, i.bytes, constraints.get(i), perByteStringEqualsHints.get(i)))
                .collect(Collectors.toList());

        // Set Z3 target
        z3.exploreTarget(targets);
    }

    public final synchronized  void setKnarrWorker(KnarrWorker knarr, ZestWorker zest) {
        this.knarr = knarr;
        this.zest = zest;
        this.z3 = new Z3Worker(zest);
//        new Thread(z3).start();
        this.notifyAll();
    }

    public Config getConfig() {
        return this.config;
    }

    public static class Input implements Serializable {
        int id;
        public byte[] bytes;
        boolean isNew;
        public LinkedList<String[]> hints;

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

        public final boolean useInvalid;

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
                useInvalid = (p.getProperty("useInvalid") != null);
            {

            }
        }
    }
}
