package edu.berkeley.cs.jqf.fuzz.central;

import edu.gmu.swe.knarr.internal.ConstraintSerializer;
import za.ac.sun.cs.green.expr.Expression;

import java.io.*;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

public class KnarrClient extends Central {

    private ConstraintSendingThread constraintSender;
    LinkedList<ConstraintPayload> constraintsToSend = new LinkedList<>();
    public KnarrClient() throws IOException {
        super();
        /**
         * WARNING: after constraintSender thread starts, oos should ONLY be used from that thread!
         */
        oos.writeObject(Type.Knarr);
        oos.flush();
        constraintSender = new ConstraintSendingThread();
        constraintSender.setDaemon(true);
        constraintSender.start();

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

    public void sendConstraints(int inputID, LinkedList<Expression> constraints, HashMap<String, String> generatedStrings) throws IOException {
        synchronized (constraintsToSend){
            constraintsToSend.add(new ConstraintPayload(inputID, constraints, generatedStrings));
            constraintsToSend.notifyAll();
        }
    }

    static class ConstraintPayload {
        int inputID;
        LinkedList<Expression> constraints;
        HashMap<String, String> generatedStrings;

        public ConstraintPayload(int inputID, LinkedList<Expression> constraints, HashMap<String, String> generatedStrings) {
            this.inputID = inputID;
            this.constraints = constraints;
            this.generatedStrings = generatedStrings;
        }
    }

    class ConstraintSendingThread extends Thread {
        public ConstraintSendingThread() {
            super("Knarr-ConstraintSender");
        }

        @Override
        public void run() {
            while (true) {
                try {
                    ConstraintPayload constraintPayload = null;
                    synchronized (constraintsToSend) {
                        while (constraintsToSend.isEmpty()) {
                            constraintsToSend.wait();
                        }
                        if (!constraintsToSend.isEmpty()) {
                            constraintPayload = constraintsToSend.pop();
                        }
                    }
                    long t1 = System.currentTimeMillis();
                    //System.out.println("Input " + constraintPayload.inputID + " constraint size: " + constraintPayload.constraints.size());
                    oos.writeInt(constraintPayload.inputID);

                    //oos.writeInt(constraints.size());
                    long doneSerializing = 0;
                    long t2 = System.currentTimeMillis();
                    try {
                        constraintSerializer.write(constraintPayload.constraints);
                        doneSerializing = System.currentTimeMillis();
                        constraintSerializer.writeTo(oos);
                    } catch (OutOfMemoryError oom) {
                        constraintSerializer.clearBuffer();
                        oom.printStackTrace();
                        oos.writeInt(4);
                        oos.writeInt(0);
                        oos.writeInt(4);
                        oos.writeInt(0);
                    }
                    //long writtenConstriants = System.currentTimeMillis();
                    //System.out.println("Wrote constraints in " + (writtenConstriants - doneSerializing));

                    oos.writeInt(constraintPayload.generatedStrings.size());
                    for (Map.Entry<String, String> entry : constraintPayload.generatedStrings.entrySet()) {
                        oos.writeUTF(entry.getKey());
                        oos.writeUTF(entry.getValue());
                    }
                    //long t2a = System.currentTimeMillis();
                    //System.out.println("Write strings to socket: " + (t2a - writtenConstriants));
                    oos.reset();
                    oos.flush();
                    constraintSerializer.clear();
                } catch (Throwable tr) {
                    tr.printStackTrace();
                }
            }
        }
    }

}
