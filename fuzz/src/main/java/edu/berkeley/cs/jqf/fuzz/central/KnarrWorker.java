package edu.berkeley.cs.jqf.fuzz.central;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

class KnarrWorker extends Worker {
    private ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
    private ArrayList<Integer> fuzzing = new ArrayList<>();
    private Coordinator c;

    public KnarrWorker(ObjectInputStream ois, ObjectOutputStream oos, Coordinator c) {
        super(ois, oos);
        this.c = c;
    }

    public LinkedList<Coordinator.Branch> getBranchCoverage(byte[] bytes, HashMap<Integer, HashSet<String>> stringEqualsArgs) throws IOException {

        // Send input to Knarr process
        oos.writeObject(bytes);
        oos.reset();
        oos.flush();

        // Get results from Knarr process
        LinkedList<Coordinator.Branch> lst;

        try {
            lst = ((LinkedList<Coordinator.Branch>)ois.readObject());
            stringEqualsArgs.putAll(((HashMap<Integer, HashSet<String>>)ois.readObject()));
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }

        return lst;
    }

    @Override
    protected void work() throws IOException, ClassNotFoundException {
        throw new Error("Shouldn't execute in separate thread");
    }
}
