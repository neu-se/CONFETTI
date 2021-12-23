package edu.berkeley.cs.jqf.fuzz.central;

import edu.gmu.swe.knarr.ConstraintDeserializer;
import edu.gmu.swe.knarr.runtime.StringUtils;
import org.apache.commons.io.input.TeeInputStream;
import org.apache.commons.io.output.NullOutputStream;
import za.ac.sun.cs.green.expr.*;

import java.io.*;
import java.util.*;
import java.util.zip.GZIPOutputStream;

public class KnarrWorker extends Worker {
    private ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
    private ArrayList<Integer> fuzzing = new ArrayList<>();
    private Coordinator c;

    private LinkedList<KnarrResponse> responses = new LinkedList<>();
    private ConstraintReceivingThread constraintReceivingThread;
    private KnarrSendingThread knarrSendingThread;

    public static int numOutstandingKnarrInputs = 0;
    private LinkedList<Coordinator.Input> pendingInputsNotSentYet = new LinkedList<>();

    private Coordinator.Config config;

    public void setConfig(Coordinator.Config config) {
        this.config = config;
        if (this.config.useConstraints && this.config.constraintsPath != null) {
            File dir = new File(this.config.constraintsPath);
            dir.mkdirs();
        }
    }

    /**
     * Encapsulates what we get back from Knarr to describe an input
     */
    static class KnarrResponse {
        public int inputID;
        public LinkedList<Expression> constraints;
        public HashMap<String, String> generatedStrings;
        public String fileName;

        public KnarrResponse(int inputID, LinkedList<Expression> constraints, HashMap<String, String> generatedStrings) {
            this.inputID = inputID;
            this.constraints = constraints;
            this.generatedStrings = generatedStrings;
        }
    }
    public KnarrWorker(ObjectInputStream ois, ObjectOutputStream oos, Coordinator c) {
        super(ois, oos);
        constraintReceivingThread = new ConstraintReceivingThread();
        constraintReceivingThread.setDaemon(true);
        constraintReceivingThread.start();
        knarrSendingThread = new KnarrSendingThread();
        knarrSendingThread.setDaemon(true);
        knarrSendingThread.start();

        this.c = c;
    }

    ConstraintDeserializer deserializer = new ConstraintDeserializer();
    static final int KNARR_MAX_QUEUE_SIZE = 5; // maximum number of outstanding requests to knarr permitted
    // this controls how much might get queued in that process. once we overflow this, we queue in this process.

    public synchronized void sendInputToKnarr(Coordinator.Input input) throws IOException {
        synchronized (this.pendingInputsNotSentYet){
            this.pendingInputsNotSentYet.add(input);
            this.pendingInputsNotSentYet.notifyAll();
        }
    }

    public KnarrResponse getConstraintsFromKnarr(){
        synchronized (responses){
            while(responses.isEmpty()){
                try {
                    responses.wait();
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }
            }
            return responses.pop();
        }
    }
    class KnarrSendingThread extends Thread {
        public KnarrSendingThread(){
            super("Knarr-ConstraintSender");
        }

        @Override
        public void run() {
            while(true){
                try{
                    synchronized (pendingInputsNotSentYet) {
                        while (pendingInputsNotSentYet.isEmpty()) {
                            pendingInputsNotSentYet.wait();
                        }
                    }
                    synchronized (responses) {
                        while (numOutstandingKnarrInputs >= KNARR_MAX_QUEUE_SIZE) {
                            responses.wait();
                        }
                    }
                    Coordinator.Input input = null;
                    synchronized (pendingInputsNotSentYet){
                        if(!pendingInputsNotSentYet.isEmpty()){
                            input = pendingInputsNotSentYet.pop();
                        }
                    }
                    if (input != null) {
                        oos.writeObject(input.bytes);
                        oos.writeObject(input.hints);
                        oos.writeObject(input.instructions);
                        oos.writeObject(input.targetedHints);
                        oos.writeInt(input.id);
                        oos.writeBoolean(input.isValid);
                        oos.reset();
                        oos.flush();
                        synchronized (responses) {
                            numOutstandingKnarrInputs++;
                        }
                    }
                } catch (Throwable tr) {
                    tr.printStackTrace();
                }
            }
        }
    }
    class ConstraintReceivingThread extends Thread {
        public ConstraintReceivingThread(){
            super("Knarr-ConstraintReceiver");
        }

        @Override
        public void run() {
            while (true) {
                try {
                    // Get constraints from Knarr process
                    LinkedList<Expression> constraints;

                    int inputID = ois.readInt();
                    OutputStream fileOrNull = NullOutputStream.NULL_OUTPUT_STREAM;
                    String filename = null;
                    if (config.useConstraints && config.constraintsPath != null) {
                        filename = config.constraintsPath + "/input_" + inputID;
                        try {
                            fileOrNull = new GZIPOutputStream(new BufferedOutputStream(new FileOutputStream(filename)));
                        } catch (FileNotFoundException e) {
                            e.printStackTrace();
                        } catch (IOException e) {
                            e.printStackTrace();
                        }
                    }

                    TeeInputStream tis = new TeeInputStream(ois, fileOrNull);
                    constraints = deserializer.fromInputStream(tis);
                    fileOrNull.close();
                    int nEntries = ois.readInt();
                    HashMap<String, String> generatedStrings = new HashMap<>();
                    for (int i = 0; i < nEntries; i++) {
                        generatedStrings.put(ois.readUTF(), ois.readUTF());
                    }

                    KnarrResponse response = new KnarrResponse(inputID, constraints, generatedStrings);

                    response.fileName = filename;
                    synchronized (responses) {
                        responses.add(response);
                        numOutstandingKnarrInputs--;
                        responses.notifyAll();
                    }
                }catch(EOFException ex){
                    ex.printStackTrace();
                    System.exit(-1);
                    return;
                } catch (Throwable tr) {
                    tr.printStackTrace();
                    System.exit(-1);
                }
            }
        }
    }

    static long constraintsProcessed;

    public static void findControllingBytes(Expression e, HashSet<Integer> bytes, HashSet<Coordinator.StringHint> stringEqualsArgs, Coordinator.Input input, Coordinator.Branch controlledBranch) {
        constraintsProcessed++;
        if (e instanceof Variable) {
            Variable v = (Variable) e;
            if (v.getName().startsWith("autoVar_")) {
                bytes.add(Integer.parseInt(v.getName().substring("autoVar_".length())));
            }
        } else if (e instanceof Operation) {
            Operation op = (Operation) e;
            if(true || controlledBranch != null) { //TODO why only when controlledBranch is not null?
                if (e.metadata != null && op.getOperator() == Operation.Operator.EQ || op.getOperator() == Operation.Operator.NE) {
                    //is this a char comparison?
                    Z3Worker.StringEqualsVisitor leftOfEQ = new Z3Worker.StringEqualsVisitor(op.getOperand(0));
                    Z3Worker.StringEqualsVisitor rightOfEQ = new Z3Worker.StringEqualsVisitor(op.getOperand(1));
                    try {
                        op.getOperand(0).accept(leftOfEQ);
                        op.getOperand(1).accept(rightOfEQ);
                    } catch (VisitorException visitorException) {
                        //visitorException.printStackTrace();
                    }

                    Z3Worker.StringEqualsVisitor symbolicString = null;
                    int comparedChar = 0;
                    if (leftOfEQ.hasSymbolicVariable() && leftOfEQ.isSimpleGeneratorFunctionExpression() && op.getOperand(1) instanceof IntConstant) {
                        symbolicString = leftOfEQ;
                        comparedChar = (int) ((IntConstant) op.getOperand(1)).getValueLong();
                    } else if (rightOfEQ.hasSymbolicVariable() && rightOfEQ.isSimpleGeneratorFunctionExpression() && op.getOperand(0) instanceof IntConstant) {
                        symbolicString = rightOfEQ;
                        comparedChar = (int) ((IntConstant) op.getOperand(0)).getValueLong();
                    }

                    if (op.getOperator() == Operation.Operator.NE && comparedChar == 0) {
                        //skip, this is just some check to make sure it's not a null char, we'll never generate that anyway...
                    } else if (symbolicString != null) {
                        Z3Worker.GeneratedCharacter symbChar = symbolicString.getSymbolicChars().getFirst();
                        String actualStr = input.generatedStrings.get(symbolicString.getFunctionName());
                        if(actualStr != null && actualStr.charAt(symbChar.index) != comparedChar && !controlledBranch.isSolved && controlledBranch.tryCharHint()) {
                            //check to make sure there is no other targeted hint for this branch for this input
                            input.targetedHints.add(new Coordinator.CharHint(comparedChar, input.generatedStrings.get(symbolicString.getFunctionName()), Coordinator.HintType.EQUALS,
                                    symbChar.bytePositionInRandomGen, symbChar.numBytesInRandomGen, symbChar.index, controlledBranch));
                        }
                    }
                }
                if (e.metadata != null && e.metadata instanceof HashSet) {
                    Iterator<StringUtils.StringComparisonRecord> it = ((HashSet<StringUtils.StringComparisonRecord>) e.metadata).iterator();
                    while (it.hasNext()) {
                        boolean ignore = false;
                        StringUtils.StringComparisonRecord cur = it.next();
                        String originalString = null;
                        //Find the right genName for this...
                        Z3Worker.StringEqualsVisitor leftOfEQ = new Z3Worker.StringEqualsVisitor(op.getOperand(0));
                        Z3Worker.StringEqualsVisitor rightOfEQ = new Z3Worker.StringEqualsVisitor(op.getOperand(1));
                        try {
                            op.getOperand(0).accept(leftOfEQ);
                            op.getOperand(1).accept(rightOfEQ);
                        } catch (VisitorException visitorException) {
                            //visitorException.printStackTrace();
                        }
                        Z3Worker.StringEqualsVisitor v = leftOfEQ;
                        if (v.getFunctionName() == null) {
                            v = rightOfEQ;
                        }
                        if (input.generatedStrings != null) {
                            if (v.getFunctionName() != null) {
                                originalString = input.generatedStrings.get(v.getFunctionName());
                            }
                        }
                        //Look and see if it will even be feasible to do this: if we want a startsWith, but the first chars are concrete
                        //or if we want an equals and there are non-symbolic chars, we should bail!
                        if (v.getNumConcreteCharsInSymbolic() > 0) {
                            ignore = true;
                        }
                        if (v.getGeneratorFunctionNames().size() > 1) {
                            ignore = true;
                        }
                        if(controlledBranch.isInFilter && controlledBranch.isSolved)
                            ignore = true;
                        if (!ignore) {
                            switch (cur.getComparisionType()) {
                                case EQUALS:
                                    if (originalString != null && !originalString.equals(cur.getStringCompared())) {
                                        //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.EQUALS, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                                        addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), Coordinator.HintType.EQUALS, controlledBranch));
                                    }
                                    break;
                                case INDEXOF:
                                    //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.INDEXOF, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                                    //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.STARTSWITH, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                                    //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.ENDSWITH, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow

                                    //TODO the indexOf comparison might have had nothing to do with this comparison, and should be ignored in that case.
                                    //We don't have a way to skip those, though. So, for now, this stays off (otherwise closure's parser brings in tons of INDEXOF /*, // */ hints that are garbage
                                    //String startsWith = cur.getStringCompared();
                                    //if (originalString != null && !originalString.contains(cur.getStringCompared())) {
                                    //    startsWith = cur.getStringCompared() + originalString;
                                    //    //addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), Coordinator.HintType.INDEXOF, controlledBranch));
                                    //    addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), startsWith, Coordinator.HintType.STARTSWITH, controlledBranch));
                                    //    //addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), endsWith, Coordinator.HintType.ENDSWITH, controlledBranch));
                                    //}
                                    break;
                                case STARTSWITH:
                                    if (originalString != null && !originalString.startsWith(cur.getStringCompared())) {
                                        String startsWith = cur.getStringCompared() + originalString;
                                        //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.STARTSWITH, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                                        addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), startsWith, Coordinator.HintType.STARTSWITH, controlledBranch));
                                    }
                                    break;
                                case ENDWITH:
                                    //if(originalString != null && !originalString.endsWith(cur.getStringCompared())){
                                    //    String endsWith = originalString + cur.getStringCompared();
                                    //    stringEqualsArgs.add(new Coordinator.StringHint(cur.getStringCompared(), endsWith, Coordinator.HintType.ENDSWITH, controlledBranch));
                                    //}
                                    break;
                                case ISEMPTY:
                                    if (originalString != null && !originalString.isEmpty()) {
                                        addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint("", Coordinator.HintType.ISEMPTY, controlledBranch));
                                    }
                                    break;
                            }

                        }
                    }
                }
            }
            for (int i = 0 ; i < op.getArity() ; i++)
                findControllingBytes(op.getOperand(i), bytes, stringEqualsArgs, input, controlledBranch);
        } else if (e instanceof FunctionCall) {
            FunctionCall f = (FunctionCall) e;
            for (Expression arg : f.getArguments())
                findControllingBytes(arg, bytes, stringEqualsArgs, input, controlledBranch);
        }
    }
    private static void addStringHintIfNew(HashSet<Coordinator.StringHint> hints, Coordinator.StringHint hintToAdd){
        int c = hintToAdd.targetBranch.addSuggestion(hintToAdd);
        hintToAdd.priority = c;
        hints.add(hintToAdd);
    }

    @Override
    protected void work() throws IOException, ClassNotFoundException {
        throw new Error("Shouldn't execute in separate thread");
    }
}
