package edu.berkeley.cs.jqf.fuzz.central;

import edu.gmu.swe.knarr.runtime.PathConditionWrapper;
import za.ac.sun.cs.green.expr.Expression;

import java.io.BufferedOutputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
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

    public void sendConstraints(LinkedList<Expression> constraints) throws IOException {
        long t1 = System.currentTimeMillis();
        System.out.println("Constraint size: " + constraints.size());
        oos.writeInt(constraints.size());
        ByteArrayOutputStream bos = new ByteArrayOutputStream(1024*100);
        ObjectOutputStream bufferredOOS = new ObjectOutputStream(bos);
        for(Expression expr : constraints){
            bufferredOOS.writeObject(expr);
        }
        bufferredOOS.flush();
        bufferredOOS.close();
        long t2 = System.currentTimeMillis();
        System.out.println("Serialize Constraints: " + (t2-t1) + " (" + bos.size() + " bytes)");
        for(Expression expr : constraints){
            oos.writeObject(expr);
        }
        long t2a = System.currentTimeMillis();
        System.out.println("Write constraints to socket: " + (t2a-t2));
        oos.reset();
        oos.flush();
    }

}
