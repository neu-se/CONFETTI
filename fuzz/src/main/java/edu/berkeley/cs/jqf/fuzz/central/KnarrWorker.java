package edu.berkeley.cs.jqf.fuzz.central;

import edu.gmu.swe.knarr.runtime.Coverage;
import org.jgrapht.alg.util.Pair;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.*;

class KnarrWorker extends Worker {
    private ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
    private ArrayList<Integer> fuzzing = new ArrayList<>();
    private Coordinator c;

    public KnarrWorker(ObjectInputStream ois, ObjectOutputStream oos, Coordinator c) {
        super(ois, oos);
        this.c = c;
    }

    public LinkedList<Expression> getConstraints(byte[] bytes, LinkedList<String[]>hints) throws IOException {
        // Send input to Knarr process
        oos.writeObject(bytes);
        oos.writeObject(hints);
        oos.reset();
        oos.flush();

        // Get constraints from Knarr process
        LinkedList<Expression> constraints;
        try {
            constraints = ((LinkedList<Expression>)ois.readObject());
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }

        return constraints;
    }

    public void process(LinkedList<Coordinator.Branch> bs, HashMap<Integer, HashSet<String>> stringEqualsArgs, Expression e) {
        Coverage.BranchData b = (Coverage.BranchData) e.metadata;

        if (b == null)
            return;

        Coordinator.Branch bb = new Coordinator.Branch();

        bb.takenID = b.takenCode;
        bb.notTakenID = b.notTakenCode;
        bb.keep = b.breaksLoop;
        bb.result = b.taken;
        bb.controllingBytes = new HashSet<>();
        bb.source = b.source;

        HashSet<String> eq = new HashSet<>();
        HashSet<String> io = new HashSet<>();

        findControllingBytes(e, bb.controllingBytes, eq);

        bs.add(bb);

        if (!eq.isEmpty()) {
            for (Integer i : bb.controllingBytes) {
                HashSet<String> cur = stringEqualsArgs.get(i);
                if (cur == null) {
                    cur = new HashSet<>();
                    stringEqualsArgs.put(i, cur);
                }
                cur.addAll(eq);
            }
        }

    }

    private void findControllingBytes(Expression e, HashSet<Integer> bytes, HashSet<String> stringEqualsArgs) {
        if (e instanceof Variable) {
            Variable v = (Variable) e;
            if (v.getName().startsWith("autoVar_")) {
                bytes.add(Integer.parseInt(v.getName().substring("autoVar_".length())));
            }
        } else if (e instanceof Operation) {
            Operation op = (Operation) e;
            if (e.metadata != null && e.metadata instanceof HashSet) {
                Iterator<Pair<String,String>> it = ((HashSet<Pair<String,String>>)e.metadata).iterator();
                while(it.hasNext()) {
                    Pair<String, String> cur = it.next();
                    switch(cur.getFirst()) {
                        case "EQUALS":
                        case "INDEXOF":
                            stringEqualsArgs.add(cur.getSecond());
                            break;
                    }

                }

            }
            for (int i = 0 ; i < op.getArity() ; i++)
                findControllingBytes(op.getOperand(i), bytes, stringEqualsArgs);
        }
    }

    @Override
    protected void work() throws IOException, ClassNotFoundException {
        throw new Error("Shouldn't execute in separate thread");
    }
}
