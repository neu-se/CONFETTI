package edu.berkeley.cs.jqf.fuzz.central;

import edu.gmu.swe.knarr.internal.ConstraintSerializer;
import za.ac.sun.cs.green.expr.Expression;

import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

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
            ret.targetedHints = (HashSet<Coordinator.TargetedHint>) ois.readObject();
            ret.id = ois.readInt();
            ret.isValid = ois.readBoolean();
            return ret;
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    private ConstraintSerializer constraintSerializer = new ConstraintSerializer();
    public void sendConstraints(LinkedList<Expression> constraints, HashMap<String, String> generatedStrings) throws IOException {
        long t1 = System.currentTimeMillis();
        System.out.println("Constraint size: " + constraints.size());
        //oos.writeInt(constraints.size());
        long t2 = System.currentTimeMillis();
        constraintSerializer.writeInt(constraints.size());
        for(Expression expr : constraints){
            constraintSerializer.write(expr);
        }
        int size = constraintSerializer.size();
        byte[] bytes = constraintSerializer.bytes();
        long doneSerializing = System.currentTimeMillis();
        System.out.println("Serialized to " + size + " bytes in " + (doneSerializing - t2));

        oos.writeInt(size);
        oos.write(bytes, 0 , size);

        long writtenConstriants = System.currentTimeMillis();
        System.out.println("Wrote constraints in " + (writtenConstriants - doneSerializing));
        oos.writeInt(generatedStrings.size());
        for(Map.Entry<String, String> entry : generatedStrings.entrySet()){
            oos.writeUTF(entry.getKey());
            oos.writeUTF(entry.getValue());
        }
        long t2a = System.currentTimeMillis();
        System.out.println("Write strings to socket: " + (t2a-writtenConstriants));
        oos.reset();
        oos.flush();
        constraintSerializer.clear();
    }

}
