package edu.berkeley.cs.jqf.fuzz.central;

import edu.gmu.swe.knarr.runtime.Coverage;
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
    public static void process(LinkedList<Coordinator.Branch> bs, HashMap<Integer, HashSet<Coordinator.StringHint>> stringEqualsArgs, Expression e, String[] filter, Coordinator.Input input) {
        Coverage.CoverageData b = (Coverage.CoverageData) e.metadata;

        if (b == null)
            return;

        for (String f : filter) {
            if (b.source != null && b.source.contains(f)) {
                return;
            }
        }

        Coordinator.Branch bb = new Coordinator.Branch(b);
        bb.controllingBytes = new HashSet<>();

        HashSet<Coordinator.StringHint> eq = new HashSet<>();

        findControllingBytes(e, bb.controllingBytes, eq, input); //TODO this can block, it's really bad when it does...
        bs.add(bb);

        if (!eq.isEmpty()) {
            for (Integer i : bb.controllingBytes) {
                HashSet<Coordinator.StringHint> cur = stringEqualsArgs.get(i);
                if (cur == null) {
                    cur = new HashSet<>();
                    stringEqualsArgs.put(i, cur);
                }
                cur.addAll(eq);
            }
        }

    }

    public static void findControllingBytes(Expression e, HashSet<Integer> bytes, HashSet<Coordinator.StringHint> stringEqualsArgs, Coordinator.Input input) {
        constraintsProcessed++;
        if (e instanceof Variable) {
            Variable v = (Variable) e;
            if (v.getName().startsWith("autoVar_")) {
                bytes.add(Integer.parseInt(v.getName().substring("autoVar_".length())));
            }
        } else if (e instanceof Operation) {
            Operation op = (Operation) e;
            if(e.metadata != null && op.getOperator() == Operation.Operator.EQ || op.getOperator() == Operation.Operator.NE){
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
                if(leftOfEQ.hasSymbolicVariable() && leftOfEQ.isSimpleGeneratorFunctionExpression() && op.getOperand(1) instanceof IntConstant){
                    symbolicString = leftOfEQ;
                    comparedChar = (int) ((IntConstant) op.getOperand(1)).getValueLong();
                }else if(rightOfEQ.hasSymbolicVariable() && rightOfEQ.isSimpleGeneratorFunctionExpression() && op.getOperand(0) instanceof IntConstant){
                    symbolicString = rightOfEQ;
                    comparedChar = (int) ((IntConstant) op.getOperand(0)).getValueLong();
                }

                if(op.getOperator() == Operation.Operator.NE && comparedChar == 0){
                    //skip, this is just some check to make sure it's not a null char, we'll never generate that anyway...
                }
                else if(symbolicString != null) {
                    Z3Worker.GeneratedCharacter symbChar = symbolicString.getSymbolicChars().getFirst();
                    input.targetedHints.add(new Coordinator.CharHint(comparedChar,input.generatedStrings.get(symbolicString.getFunctionName()), Coordinator.HintType.EQUALS,
                            symbChar.bytePositionInRandomGen, symbChar.numBytesInRandomGen, symbChar.index));
                }
            }
            if (e.metadata != null && e.metadata instanceof HashSet) {
                Iterator<StringUtils.StringComparisonRecord> it = ((HashSet<StringUtils.StringComparisonRecord>)e.metadata).iterator();
                while(it.hasNext()) {
                    StringUtils.StringComparisonRecord cur = it.next();
                    switch(cur.getComparisionType()) {
                        case EQUALS:
                            //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.EQUALS, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                            stringEqualsArgs.add(new Coordinator.StringHint(cur.getStringCompared(), Coordinator.HintType.EQUALS));
                            break;
                        case INDEXOF:
                            //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.INDEXOF, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                            //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.STARTSWITH, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                            //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.ENDSWITH, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow

                            stringEqualsArgs.add(new Coordinator.StringHint(cur.getStringCompared(), Coordinator.HintType.INDEXOF));
                            stringEqualsArgs.add(new Coordinator.StringHint(cur.getStringCompared(), Coordinator.HintType.STARTSWITH));
                            stringEqualsArgs.add(new Coordinator.StringHint(cur.getStringCompared(), Coordinator.HintType.ENDSWITH));
                            break;
                        case STARTSWITH:
                            //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.STARTSWITH, KnarrGuidance.extractChoices(e))); //TODO disable when not debugging, this is slow
                            stringEqualsArgs.add(new Coordinator.StringHint(cur.getStringCompared(), Coordinator.HintType.STARTSWITH));
                            break;
                        //case ENDSWITH:
                            //stringEqualsArgs.add(new Coordinator.StringHint(cur.getSecond(), Coordinator.HintType.ENDSWITH));
                            //break;
                        case ISEMPTY:
                            stringEqualsArgs.add(new Coordinator.StringHint("", Coordinator.HintType.ISEMPTY));
                            break;
                    }

                }

            }
            for (int i = 0 ; i < op.getArity() ; i++)
                findControllingBytes(op.getOperand(i), bytes, stringEqualsArgs, input);
        } else if (e instanceof FunctionCall) {
            FunctionCall f = (FunctionCall) e;
            for (Expression arg : f.getArguments())
                findControllingBytes(arg, bytes, stringEqualsArgs, input);
        }
    }

    @Override
    protected void work() throws IOException, ClassNotFoundException {
        throw new Error("Shouldn't execute in separate thread");
    }
}
