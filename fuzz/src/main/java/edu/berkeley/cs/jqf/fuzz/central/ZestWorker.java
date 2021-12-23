package edu.berkeley.cs.jqf.fuzz.central;

import edu.berkeley.cs.jqf.fuzz.guidance.Result;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.*;

class ZestWorker extends Worker {
    private ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
    private ArrayList<Integer> fuzzing = new ArrayList<>();
    private ArrayList<TreeSet<Integer>> recommendations = new ArrayList<>();
    private LinkedList<Integer> newlyRecommendedInputsToQueue = new LinkedList<>();
    private HashSet<Integer> allRecommendedInputs = new HashSet<>();
    private ArrayList<HashMap<Integer, HashSet<Coordinator.StringHint>>> stringEqualsHints = new ArrayList<>();
    private Coordinator c;

    private final Coordinator.StringHint[] EMPTY = new Coordinator.StringHint[0];

    private LinkedList<Coordinator.Input> fromZ3 = new LinkedList<>();
    private LinkedList<Coordinator.Input> updatedScoreInputs = new LinkedList<>();

    public ZestWorker(ObjectInputStream ois, ObjectOutputStream oos, Coordinator c) throws IOException {
        super(ois, oos);
        this.c = c;
    }

    /**
     * These are inputs that we WANT to recommend, but haven't yet because the client hasn't yet checked in
     * @return
     */
    public LinkedList<Integer> getNewlyRecommendedInputsToQueue() {
        return newlyRecommendedInputsToQueue;
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
                    LinkedList<int[]> instructions = (LinkedList<int[]>) ois.readObject();
                    LinkedList<Coordinator.TargetedHint> targetedHints = (LinkedList<Coordinator.TargetedHint>) ois.readObject();

                    Double coveragePercentage = ois.readDouble();
                    Long numExecutions = ois.readLong();
                    Integer score = ois.readInt();

                    // Receive coverage
                    //                Coverage cov = (Coverage) ois.readObject();

                    // Save input
                    if(id > inputs.size()){
                        //If we are running with pre-hinted seeds, we won't have the inputs on this side, but that is probably OK
                        //just grow the arraylist to fit this... old behavior was to die in this case
                        while(inputs.size() < id){
                            inputs.add(null);
                            fuzzing.add(null);
                            recommendations.add(new TreeSet<>());
                            stringEqualsHints.add(null);
                        }
                        //throw new IllegalArgumentException();
                    }
                    inputs.add(id, inputRequests);
                    fuzzing.add(id, 0);

                    // Let coordinator thread know
                    int size_sendinput = 0;
                    for (byte[] b : inputRequests)
                        size_sendinput += b.length;
                    byte[] bs = new byte[size_sendinput];
                    int i = 0;
                    LinkedList<int[]> requestOffsets = new LinkedList<int[]>();
                    for (byte[] b : inputRequests) {
                        requestOffsets.add(new int[]{i, b.length});
                        System.arraycopy(b, 0, bs, i, b.length);
                        i += b.length;
                    }

                    c.foundInput(id, bs, res != Result.INVALID, hints, instructions, targetedHints, coveragePercentage, numExecutions, score, requestOffsets);


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

                    if(inputs.get(selected) == null){
                        oos.writeObject(null);
                        oos.writeObject(null);
                        oos.writeObject(null);
                        break;
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
                    //Flatten the list and sort it.

                    // The parallel list structure is somewhat archaic and made sense for a different hinting strategy
                    // good target to refactor in the future.
                    // Each one of the hints will be tried independently, so it doesn't really matter to keep them grouped
                    // or sorted by their position in the input. Instead, we'll sort them by how many times we've made
                    // that same hint suggestion to target the same branch (across all inputs). We don't update that
                    // data as fuzzing progresses, but assume instead that as the corpus grows, we'll also eventually
                    // execute all hints.

                    ArrayList<HintWithPosition> flattendHints = new ArrayList<>(instructionsToSend.size());
                    Iterator<int[]> insnIter = instructionsToSend.iterator();
                    Iterator<Coordinator.StringHint[]> hintIter = stringsToSend.iterator();
                    while(insnIter.hasNext()){
                        int[] pos = insnIter.next();
                        Coordinator.StringHint[] h = hintIter.next();
                        if(h == null){
                            flattendHints.add(new HintWithPosition(null, pos));
                        }else{
                            for(Coordinator.StringHint _h : h){
                                flattendHints.add(new HintWithPosition(_h, pos));
                            }
                        }
                    }
                    flattendHints.sort(HintWithPosition::compareTo);
                    instructionsToSend.clear();
                    stringsToSend.clear();
                    for(HintWithPosition h : flattendHints){
                        instructionsToSend.add(h.pos);
                        stringsToSend.add(new Coordinator.StringHint[]{h.hint});
                    }


                    // Get the Coordinator.Input object corrseponding to the selected so we can get any
                    // previously used hints
                    Coordinator.Input in = c.getInput(selected);

                    //if((stringsToSend != null && stringsToSend.size() > 0) || (in.hints != null && in.hints.size() > 0)){
                    //    System.out.println(in.id + " hints sent!");
                    //    System.out.println(stringsToSend);
                    //    System.out.println(in.hints);
                    //}
                    // Send instructions
                    oos.writeObject(instructionsToSend);
                    oos.writeObject(stringsToSend);     // Strings that are new hints
                    oos.writeObject(in == null || in.targetedHints == null ? new HashSet<>() : in.targetedHints);

                    // Update state
                    fuzzing.set(selected, (toFuzz + 1) % inputs.get(selected).size());
                    break;

                case GETZ3INPUT:
                    // Zest is asking if there's an input we'd like to explore now
                    Coordinator.Input next;
                    synchronized (fromZ3) {
                        next = (fromZ3.isEmpty() ? null : fromZ3.removeFirst());
                    }
                    //if (next != null) {
                        //System.out.println("WIN");
                        //System.out.println(next.hintGroups);
                    //}

                    oos.writeObject(next);
                    break;
                case GETRECOMMENDATIONS:
                    synchronized (recommendations){
                        //if(!newlyRecommendedInputsToQueue.isEmpty())
                        //    System.out.println("Recommending inputs: " + newlyRecommendedInputsToQueue);
                        oos.writeObject(newlyRecommendedInputsToQueue);
                        newlyRecommendedInputsToQueue.clear();
                    }
                    break;
                case GETSCOREUPDATES:
                    // Zest is asking if there's an Inputs whose scores we should update
                    Coordinator.Input n;
                    synchronized (updatedScoreInputs) {

                        while(true) {
                            n = (updatedScoreInputs.isEmpty() ? null : updatedScoreInputs.removeFirst());
                            //if (n != null) {
                                //System.out.println("SCORE UPDATES FOR INPUTS BEING SENT");
                            //}
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
    class HintWithPosition implements Comparable<HintWithPosition>{
        Coordinator.StringHint hint;
        int[] pos;

        @Override
        public String toString() {
            return "HintWithPosition{" +
                    "hint=" + hint +
                    ", pos=" + Arrays.toString(pos) +
                    '}';
        }

        public HintWithPosition(Coordinator.StringHint hint, int[] pos) {
            this.hint = hint;
            this.pos = pos;
        }

        @Override
        public int compareTo(HintWithPosition o) {
            if (this.hint == null && o.hint == null)
                return 0;
            if (this.hint == null && o.hint != null)
                return 1;
            if (this.hint != null && o.hint == null)
                return -1;
            if (this.hint.priority == o.hint.priority)
                return 0;
            if (this.hint.priority > o.hint.priority)
                return 1;
            return -1;
        }
    }
    public void recommend(int inputID, TreeSet<Integer> recommendation, HashMap<Integer, HashSet<Coordinator.StringHint>> eqs) {
        synchronized (recommendations) {
            if(!(recommendation.isEmpty() && eqs.isEmpty()) && allRecommendedInputs.add(inputID)){
                newlyRecommendedInputsToQueue.add(inputID);
            }
            recommendations.set(inputID, recommendation);
            stringEqualsHints.set(inputID, eqs);
        }
    }

    public void addInputFromZ3(Coordinator.Input z3Input, Coordinator.Input originalInput) {
        synchronized (fromZ3) {
            // z3 might have lost constraints on the strings besides the ones that we wanted.
            // as a heuristic: we'll try to execute the exact input we got from z3, but then also try each string
            // one by one
            fromZ3.add(z3Input);
            for(Coordinator.StringHintGroup sh : z3Input.hintGroups){
                if(sh.hints.size() == 1)
                    continue;
                for(int i = 0; i < sh.hints.size(); i++){
                    Coordinator.Input originalWithOneHint = new Coordinator.Input();
                    originalWithOneHint.hints = new LinkedList<>(originalInput.hints);
                    originalWithOneHint.instructions = new LinkedList<>(originalInput.instructions);
                    originalWithOneHint.bytes = originalInput.bytes;
                    originalWithOneHint.addOrReplaceHint(sh.hints.get(i), sh.instructions.get(i));
                    fromZ3.add(originalWithOneHint);
                }
            }
        }
    }

    public void addUpdatedInputScore(Coordinator.Input i ) {
        synchronized (updatedScoreInputs) {
            updatedScoreInputs.add(i);
        }
    }
}
