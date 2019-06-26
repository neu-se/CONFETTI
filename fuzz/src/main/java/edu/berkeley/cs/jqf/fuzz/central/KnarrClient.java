package edu.berkeley.cs.jqf.fuzz.central;

import za.ac.sun.cs.green.expr.Expression;

import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class KnarrClient extends Central {

    public KnarrClient() throws IOException {
        super();
        oos.writeObject(Type.Knarr);
        oos.flush();
    }
    public byte[] getInput() throws IOException {
        try {
            return (byte[]) ois.readObject();
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    public void sendConstraints(LinkedList<Expression> constraints) throws IOException {
        oos.writeObject(constraints);
        oos.reset();
        oos.flush();
    }
}
