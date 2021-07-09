package edu.berkeley.cs.jqf.fuzz.central;

import edu.gmu.swe.knarr.runtime.PathConditionWrapper;
import za.ac.sun.cs.green.expr.Expression;

import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;

public class KnarrClient extends Central {

    public KnarrClient() throws IOException {
        super();
        oos.writeObject(Type.Knarr);
        oos.flush();
    }
    public Coordinator.Input getInput() throws IOException {
        try {
            Coordinator.Input ret = new Coordinator.Input();
            ret.bytes = (byte[]) ois.readObject();
            ret.hints = (LinkedList<Coordinator.StringHint[]>) ois.readObject();
            ret.instructions = (LinkedList<int[]>) ois.readObject();
            ret.id = ois.readInt();
            ret.isValid = ois.readBoolean();
            return ret;
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    public void sendConstraints(LinkedList<Expression> constraints, LinkedList<int[]> varsUsedInControlFlowOfGenerator) throws IOException {
        oos.writeObject(constraints);
        oos.writeObject(varsUsedInControlFlowOfGenerator);
        oos.reset();
        oos.flush();
    }
}
