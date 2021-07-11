package edu.berkeley.cs.jqf.fuzz.central;

import edu.berkeley.cs.jqf.fuzz.knarr.KnarrGuidance;
import edu.gmu.swe.knarr.runtime.Coverage;
import edu.gmu.swe.knarr.runtime.StringUtils;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.FunctionCall;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;

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

    public synchronized LinkedList<Expression> getConstraints(Coordinator.Input input) throws IOException {
        // Send input to Knarr process
        oos.writeObject(input.bytes);
        oos.writeObject(input.hints);
        oos.writeObject(input.instructions);
        oos.writeInt(input.id);
        oos.writeBoolean(input.isValid);
        oos.reset();
        oos.flush();

        // Get constraints from Knarr process
        LinkedList<Expression> constraints;
        LinkedList<int[]> requestsForRandom;
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

    static long constraintsProcessed;
    public static void process(LinkedList<Coordinator.Branch> bs, HashMap<Integer, HashSet<Coordinator.StringHint>> stringEqualsArgs, Expression e, String[] filter) {
        Coverage.BranchData b = (Coverage.BranchData) e.metadata;

        if (b == null)
            return;

        for (String f : filter) {
            if (b.source != null && b.source.contains(f)) {
                return;
            }
        }

        Coordinator.Branch bb = new Coordinator.Branch();

        bb.takenID = b.takenCode;
        bb.notTakenID = b.notTakenCode;
        bb.keep = b.breaksLoop;
        bb.result = b.taken;
        bb.controllingBytes = new HashSet<>();
        bb.source = b.source;

        HashSet<Coordinator.StringHint> eq = new HashSet<>();

        findControllingBytes(e, bb.controllingBytes, eq); //TODO this can block, it's really bad when it does...
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

    public static void findControllingBytes(Expression e, HashSet<Integer> bytes, HashSet<Coordinator.StringHint> stringEqualsArgs) {
        constraintsProcessed++;
        if (e instanceof Variable) {
            Variable v = (Variable) e;
            if (v.getName().startsWith("autoVar_")) {
                bytes.add(Integer.parseInt(v.getName().substring("autoVar_".length())));
            }
        } else if (e instanceof Operation) {
            Operation op = (Operation) e;
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
                findControllingBytes(op.getOperand(i), bytes, stringEqualsArgs);
        } else if (e instanceof FunctionCall) {
            FunctionCall f = (FunctionCall) e;
            for (Expression arg : f.getArguments())
                findControllingBytes(arg, bytes, stringEqualsArgs);
        }
    }

    @Override
    protected void work() throws IOException, ClassNotFoundException {
        throw new Error("Shouldn't execute in separate thread");
    }
}
