package edu.berkeley.cs.jqf.fuzz.central;

import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance;
import edu.berkeley.cs.jqf.fuzz.guidance.Result;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.TreeSet;

class ZestWorker extends Worker {
    private ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
    private ArrayList<Integer> fuzzing = new ArrayList<>();
    private ArrayList<TreeSet<Integer>> recommendations = new ArrayList<>();
    private ArrayList<HashMap<Integer, HashSet<Coordinator.StringHint>>> stringEqualsHints = new ArrayList<>();
    private Coordinator c;

    private final Coordinator.StringHint[] EMPTY = new Coordinator.StringHint[0];

    private LinkedList<Coordinator.Input> fromZ3 = new LinkedList<>();
    private LinkedList<Coordinator.Input> updatedScoreInputs = new LinkedList<>();

    public ZestWorker(ObjectInputStream ois, ObjectOutputStream oos, Coordinator c) throws IOException {
        super(ois, oos);
        this.c = c;
    }

    @Override
    public void work() throws IOException, ClassNotFoundException {

        while (true) {
            // Receive input or select new input


            oos.flush();
            oos.reset();
            ZestMessageType messageType = (ZestMessageType) ois.readObject();
            if (messageType == null) continue;

            switch(messageType) {

//                case HEARTBEAT:
//                    // Receive total executions and send whether z3 thread has started
//                    Long heartbeatNumExecutions = ois.readLong();
//                    Double heartbeatCoveragePercentage = ois.readDouble();
//                    c.handleHeartbeat(heartbeatNumExecutions, heartbeatCoveragePercentage);
//                    if(c.z3Started)
//                        oos.writeObject(c.z3StartedInputCount);
//                    else
//                        oos.writeObject(null);
//                    break;


                case SENDINPUT:
                    // Receive input
                    LinkedList<byte[]> inputRequests = (LinkedList<byte[]>) ois.readObject();
                    Result res = (Result) ois.readObject();
                    int id = ois.readInt();

                    LinkedList<Coordinator.StringHint[]> hints = (LinkedList<Coordinator.StringHint[]>) ois.readObject();

                    Double coveragePercentage = ois.readDouble();
                    Long numExecutions = ois.readLong();
                    Integer score = ois.readInt();

                    // Receive coverage
                    //                Coverage cov = (Coverage) ois.readObject();

                    // Save input
                    inputs.add(id, inputRequests);
                    fuzzing.add(id, 0);

                    // Let coordinator thread know
                    int size_sendinput = 0;
                    for (byte[] b : inputRequests)
                        size_sendinput += b.length;
                    byte[] bs = new byte[size_sendinput];
                    int i = 0;
                    for (byte[] b : inputRequests) {
                        System.arraycopy(b, 0, bs, i, b.length);
                        i += b.length;
                    }

                    c.foundInput(id, bs, res != Result.INVALID, hints, coveragePercentage, numExecutions, score);


                    synchronized (recommendations) {
                        recommendations.add(new TreeSet<>());
                        stringEqualsHints.add(null);
                    }
                    break;

                case SELECTINPUT:
                    // Select input
                    int selected = (Integer) ois.readObject();

                    // Select part of the input to fuzz
                    int offset = 0;
                    int toFuzz = fuzzing.get(selected);
                    LinkedList<int[]> instructionsToSend = new LinkedList<>();
                    LinkedList<Coordinator.StringHint[]> stringsToSend = new LinkedList<>();
                    TreeSet<Integer> recs;
                    synchronized (recommendations) {
                        recs = recommendations.get(selected);
                    }

                    HashMap<Integer, HashSet<Coordinator.StringHint>> inputStrings = stringEqualsHints.get(selected);

                    for (byte[] b : inputs.get(selected)) {
                        if (!recs.isEmpty()) {
                            boolean addThis = false;

                            for (int j = offset; j < offset + b.length; j++) {
                                addThis = recs.contains(j);

                                if (addThis)
                                    break;
                            }

                            if (!addThis) {
                                offset += b.length;
                                continue;
                            }

                            instructionsToSend.addLast(new int[]{offset, b.length});
                            if (inputStrings != null && inputStrings.containsKey(offset))
                                stringsToSend.addLast(inputStrings.get(offset).toArray(new Coordinator.StringHint[0]));
                            else
                                stringsToSend.addLast(EMPTY);
                        }

                        offset += b.length;
                    }

                    // Get the Coordinator.Input object corrseponding to the selected so we can get any
                    // previously used hints
                    Coordinator.Input in = c.getInput(selected);

                    // Send instructions
                    oos.writeObject(instructionsToSend);
                    oos.writeObject(stringsToSend);     // Strings that are new hints
                    oos.writeObject(in.hints);          // Strings that are previously used hints that must be replicated

                    printSentStringHints(stringsToSend);

                    // Update state
                    fuzzing.set(selected, (toFuzz + 1) % inputs.get(selected).size());
                    break;

                case GETZ3INPUT:
                    // Zest is asking if there's an input we'd like to explore now
                    Coordinator.Input next;
                    synchronized (fromZ3) {
                        next = (fromZ3.isEmpty() ? null : fromZ3.removeFirst());
                    }
                    if (next != null) {
                        System.out.println("WIN");
                        printSentStringHints(next.hints);
                    }

                    oos.writeObject(next);
                    break;

                case GETSCOREUPDATES:
                    // Zest is asking if there's an Inputs whose scores we should update
                    Coordinator.Input n;
                    synchronized (updatedScoreInputs) {

                        while(true) {
                            n = (updatedScoreInputs.isEmpty() ? null : updatedScoreInputs.removeFirst());
                            if (n != null) {
                                System.out.println("SCORE UPDATES FOR INPUTS BEING SENT");
                            }
                            oos.writeObject(n);
                            if(n == null) break;
                        }
                    }

                    break;

                default:
                    break;
            }
        }
    }

    private void printSentStringHints(LinkedList<Coordinator.StringHint[]> stringHintsSent) {
        if (stringHintsSent.isEmpty())
            return;

        System.out.print("\tSent strings: ");
        for (Coordinator.StringHint[] s : stringHintsSent) {
            if (s.length == 0)
                continue;

            System.out.print("[ ");
            for (Coordinator.StringHint ss : s)
                System.out.print(ss.getHint() + ", " + ss.getType().toString());
            System.out.print("] ");
        }

        System.out.println();
    }

    public void recommend(int inputID, TreeSet<Integer> recommendation, HashMap<Integer, HashSet<Coordinator.StringHint>> eqs) {
        synchronized (recommendations) {
            recommendations.set(inputID, recommendation);
            stringEqualsHints.set(inputID, eqs);
        }
    }

    public void addInputFromZ3(Coordinator.Input i) {
        synchronized (fromZ3) {
            fromZ3.add(i);
        }
    }

    public void addUpdatedInputScore(Coordinator.Input i ) {
        synchronized (updatedScoreInputs) {
            updatedScoreInputs.add(i);
        }
    }
}
