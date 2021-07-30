package edu.berkeley.cs.jqf.fuzz.central;

import edu.gmu.swe.knarr.runtime.StringUtils;
import za.ac.sun.cs.green.expr.*;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.*;

public class KnarrWorker extends Worker {
    private ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
    private ArrayList<Integer> fuzzing = new ArrayList<>();
    private Coordinator c;

    public KnarrWorker(ObjectInputStream ois, ObjectOutputStream oos, Coordinator c) {
        super(ois, oos);
        this.c = c;
    }

    public LinkedList<Expression> getConstraints(Coordinator.Input input) throws IOException {
        // Send input to Knarr process
        oos.writeObject(input.bytes);
        oos.writeObject(input.hints);
        oos.writeObject(input.instructions);
        oos.writeObject(input.targetedHints);
        oos.writeInt(input.id);
        oos.writeBoolean(input.isValid);
        oos.reset();
        oos.flush();

        // Get constraints from Knarr process
        LinkedList<Expression> constraints;
        try {
            int nConstraints = ois.readInt();
            constraints = new LinkedList<Expression>();
            for(int i = 0; i < nConstraints; i++){
                constraints.add((Expression) ois.readObject());
            }
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }

        return constraints;
    }
    public HashMap<String, String> getGeneratedStrings() throws IOException {
        int nEntries = ois.readInt();
        HashMap<String, String> ret = new HashMap<>();
        for(int i = 0; i < nEntries; i++){
            ret.put(ois.readUTF(), ois.readUTF());
        }
        return ret;
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
            if(controlledBranch != null && !controlledBranch.isSolved) {
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
                        //TODO this seems like more noise than utility
                        //input.targetedHints.add(new Coordinator.CharHint(comparedChar, input.generatedStrings.get(symbolicString.getFunctionName()), Coordinator.HintType.EQUALS,
                        //        symbChar.bytePositionInRandomGen, symbChar.numBytesInRandomGen, symbChar.index));
                    }
                }
                if (e.metadata != null && e.metadata instanceof HashSet) {
                    Iterator<StringUtils.StringComparisonRecord> it = ((HashSet<StringUtils.StringComparisonRecord>) e.metadata).iterator();
                    while (it.hasNext()) {
                        StringUtils.StringComparisonRecord cur = it.next();
                        String originalString = null;
                        if (input.generatedStrings != null) {
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
                            if (v.getFunctionName() != null) {
                                originalString = input.generatedStrings.get(v.getFunctionName());
                            }
                        }
                        switch (cur.getComparisionType()) {
                            case EQUALS:
                                if (originalString == null || !originalString.equals(cur.getStringCompared())) {
                                    //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.EQUALS, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                                    addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), Coordinator.HintType.EQUALS, controlledBranch));
                                }
                                break;
                            case INDEXOF:
                                //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.INDEXOF, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                                //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.STARTSWITH, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                                //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.ENDSWITH, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow

                                String startsWith = cur.getStringCompared();
                                if(originalString != null){
                                    startsWith = cur.getStringCompared() + originalString;
                                }
                                String endsWith = cur.getStringCompared();
                                if(originalString != null){
                                    endsWith = originalString + cur.getStringCompared();
                                }
                                addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), Coordinator.HintType.INDEXOF, controlledBranch));
                                addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), startsWith, Coordinator.HintType.STARTSWITH, controlledBranch));
                                addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), endsWith, Coordinator.HintType.ENDSWITH, controlledBranch));
                                break;
                            case STARTSWITH:
                                if (originalString == null || !originalString.startsWith(cur.getStringCompared())) {
                                    startsWith = cur.getStringCompared();
                                    if(originalString != null){
                                        startsWith = cur.getStringCompared() + originalString;
                                    }
                                    //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.STARTSWITH, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                                    addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint(cur.getStringCompared(), startsWith, Coordinator.HintType.STARTSWITH, controlledBranch));
                                }
                                break;
                            //case ENDSWITH:
                            //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.ENDSWITH));
                            //break;
                            case ISEMPTY:
                                //if (originalString == null || !originalString.isEmpty()) {
                                //    addStringHintIfNew(stringEqualsArgs, new Coordinator.StringHint("", Coordinator.HintType.ISEMPTY, controlledBranch));
                                //}
                                break;
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
        if(hintToAdd.targetBranch != null && hintToAdd.targetBranch.addSuggestion(hintToAdd))
            hints.add(hintToAdd);
    }

    @Override
    protected void work() throws IOException, ClassNotFoundException {
        throw new Error("Shouldn't execute in separate thread");
    }
}
