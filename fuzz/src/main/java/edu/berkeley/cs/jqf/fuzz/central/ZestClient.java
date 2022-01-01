package edu.berkeley.cs.jqf.fuzz.central;

import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance;
import edu.berkeley.cs.jqf.fuzz.guidance.GuidanceException;
import edu.berkeley.cs.jqf.fuzz.guidance.RecordingInputStream;
import edu.berkeley.cs.jqf.fuzz.guidance.Result;
import edu.berkeley.cs.jqf.fuzz.util.Coverage;
import org.eclipse.collections.impl.list.mutable.primitive.ByteArrayList;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;

import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

public class ZestClient extends Central {

       public Integer triggerZ3SampleWindow;
       public Double triggerZ3SampleThreshold;
    public ZestClient() throws IOException  {
        super();
        oos.writeObject(Type.Zest_Initial);
        oos.flush();
        oos.reset();
        try {
            triggerZ3SampleWindow = (Integer) ois.readObject();
            triggerZ3SampleThreshold = (Double) ois.readObject();
        } catch(Exception e) {}


    }
//
//    public void sendHeartBeat(Long numExecutions, Double currentCoverage) throws IOException {
//        oos.writeObject(ZestMessageType.HEARTBEAT);
//        oos.writeLong(numExecutions);
//        oos.writeDouble(currentCoverage);
//        oos.reset();
//        oos.flush();
//    }
//
//    public Long receiveZ3Started() throws IOException {
//        try {
//            return (Long)ois.readObject();
//
//        } catch (ClassNotFoundException e) {
//            e.printStackTrace();
//        }
//
//        return null;
//    }
//
//    public void activate() throws IOException {
//        oos.writeObject(Type.Zest);
//        oos.flush();
//
//    }

    /* Client:
     * 1. Send input
     * 2. Send coverage
     * 3. Select input
     * 3. Receive instructions
     */
    public void sendInput(RecordingInputStream.MarkedInput recorded, Result result, ZestGuidance.Input input, double coveragePercentage, long totalExecutions) throws IOException {
        oos.writeObject(ZestMessageType.SENDINPUT);
        oos.writeObject(recorded);
        oos.writeObject(result);
        oos.writeInt(input.id);
        oos.writeObject(input.stringEqualsHints == null ? new LinkedList<Coordinator.StringHint[]>() : input.stringEqualsHints);
        oos.writeObject(input.instructions == null ? new LinkedList<int[]>() : input.instructions);
        oos.writeObject((input.appliedTargetedHints == null ? new LinkedList<Coordinator.TargetedHint>() : input.appliedTargetedHints));
        oos.writeDouble(coveragePercentage);
        oos.writeLong(totalExecutions);
        oos.writeInt(input.score);
        oos.flush();
        oos.reset();
    }

    private boolean hasSeenNullZ3Input = false;

    public void selectInput(int id) throws IOException {
        oos.writeObject(ZestMessageType.SELECTINPUT);
        oos.writeObject(new Integer(id));
        oos.flush();
        hasSeenNullZ3Input = false;
    }

    public LinkedList<int[]> receiveInstructions() throws IOException {
        try {
            return (LinkedList<int[]>) ois.readObject();
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }


    public LinkedList<Coordinator.StringHint[]> receiveStringEqualsHints() throws IOException {
        try {
            return (LinkedList<Coordinator.StringHint[]>) ois.readObject();
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    public LinkedList<Coordinator.StringHint[]> receivePreviouslyUsedStringEqualsHints() throws IOException {
        try {
            return (LinkedList<Coordinator.StringHint[]>) ois.readObject();
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    public LinkedList<int[]> receiveByteRangesUsedAsControlInGenerator() throws IOException {
        try {
            return (LinkedList<int[]>) ois.readObject();
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    public HashSet<Coordinator.TargetedHint> receiveTargetedHints() throws IOException {
        try {
            return (HashSet<Coordinator.TargetedHint>) ois.readObject();
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    public void sendCoverage(Coverage totalCoverage) {
        // TODO
    }

    public List<Coordinator.Input> getScoreUpdates() {

        try {

            LinkedList<Coordinator.Input> ret = new LinkedList<>();
            oos.writeObject(ZestMessageType.GETSCOREUPDATES);
            oos.flush();
            oos.reset();
            Coordinator.Input i = (Coordinator.Input) ois.readObject();
            while(i != null) {
                ret.add(i);
                i = (Coordinator.Input) ois.readObject();
            }

            return ret;

        } catch (ClassNotFoundException e) {
            throw new Error(e);
        } catch (IOException e) {
            return new LinkedList<>();
        }
    }

    /* If things are going very fast, it's likely that there will be some GC pauses on central,
    reducing how often we reach out reduces the likelihood of us eating the big cheese, too,
    while that pause happens.*/
    private static final int MIN_TIME_BEFORE_BUGGING_CENTRAL = 2000; //msec..
    private long lastCentralGetInputCall;
    private long lastCentralGetRecsCall;
    public Coordinator.Input getInput() {
        long now = System.currentTimeMillis();
        if(hasSeenNullZ3Input && now < lastCentralGetInputCall + MIN_TIME_BEFORE_BUGGING_CENTRAL)
            return null;
        lastCentralGetInputCall = now;

        try {
            oos.writeObject(ZestMessageType.GETZ3INPUT);
            oos.flush();
            oos.reset();
            Coordinator.Input ret = (Coordinator.Input) ois.readObject();

            if (ret == null)
                hasSeenNullZ3Input = true;

            return ret;
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        } catch (IOException e) {
            throw new GuidanceException(e);
        }
    }

    public LinkedList<Integer> getRecommendations() {
        long now = System.currentTimeMillis();
        if(now < lastCentralGetRecsCall + MIN_TIME_BEFORE_BUGGING_CENTRAL)
            return new LinkedList<>();
        lastCentralGetRecsCall = now;
        try {
            oos.writeObject(ZestMessageType.GETRECOMMENDATIONS);
            oos.flush();
            oos.reset();
            LinkedList<Integer> ret = (LinkedList<Integer>) ois.readObject();
            if(ret == null)
                ret = new LinkedList<>();

            return ret;
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        } catch (IOException e) {
            return null;
        }
    }

}
