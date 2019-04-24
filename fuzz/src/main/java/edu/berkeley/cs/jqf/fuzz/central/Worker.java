package edu.berkeley.cs.jqf.fuzz.central;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

abstract class Worker implements Runnable {
    protected final ObjectInputStream ois;
    protected final ObjectOutputStream oos;

    public Worker(ObjectInputStream ois, ObjectOutputStream oos) {
        this.ois = ois;
        this.oos = oos;
    }

    @Override
    public void run() {
        try {
            this.work();
        } catch (IOException | ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    protected abstract void work() throws IOException, ClassNotFoundException;
}
