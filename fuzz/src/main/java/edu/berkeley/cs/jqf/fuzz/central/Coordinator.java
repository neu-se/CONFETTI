package edu.berkeley.cs.jqf.fuzz.central;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

class Coordinator implements Runnable {
    private HashMap<Integer, Input> inputs = new HashMap<>();

    protected final synchronized void foundInput(int id, byte[] bytes) {
        Input in = new Input();
        in.bytes = bytes;
        in.coverage = null;
        this.inputs.put(id, in);
        this.notifyAll();

        System.out.println("Input added " + id);
    }

    @Override
    public void run() {

        while (true) {
            Map<Integer, Input> m;

            synchronized (this) {
                try {
                    this.wait();
                } catch (InterruptedException e) {
                    // Nothing
                }

                m = Collections.unmodifiableMap(inputs);
            }

            for (Map.Entry<Integer, Input> entry : m.entrySet()) {
                if (entry.getValue().coverage == null) {
                    // Compute coverage and branches with Knarr

                    // Check if any previous branches were explored
                }
            }
        }
    }

    private static class Input {
        byte[] bytes;
        Object coverage;
        HashSet<Branch> branches;
    }

    private static class Branch {
        long id;
        boolean trueExplored;
        boolean falseExplored;

        LinkedList<Integer> bytesControlling;
    }
}
