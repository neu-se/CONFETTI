package edu.berkeley.cs.jqf.fuzz.knarr;

import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.central.KnarrClient;
import edu.berkeley.cs.jqf.fuzz.guidance.Guidance;
import edu.berkeley.cs.jqf.fuzz.guidance.GuidanceException;
import edu.berkeley.cs.jqf.fuzz.guidance.Result;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEvent;
import edu.gmu.swe.knarr.runtime.Coverage;
import edu.gmu.swe.knarr.runtime.PathUtils;
import edu.gmu.swe.knarr.runtime.Symbolicator;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;
import za.ac.sun.cs.green.expr.Variable;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.function.Consumer;

public class KnarrGuidance implements Guidance {
    private byte[] input;
    private KnarrClient client;

    public KnarrGuidance() throws IOException  {
        this.client = new KnarrClient();
    }

    @Override
    public InputStream getInput() throws IllegalStateException, GuidanceException {
        Symbolicator.reset();
        return new TaintingInputStream(new ByteArrayInputStream(this.input));
    }

    @Override
    public boolean hasInput() {
        try {
            this.input = client.getInput();
        } catch (IOException e) {
            throw new Error(e);
        }

        return true;
    }

    @Override
    public void handleResult(Result result, Throwable error) throws GuidanceException {
        Expression constraints = PathUtils.getCurPC().constraints;

        System.out.println(result);

        LinkedList<Coordinator.Branch> branches = new LinkedList<>();

        // Get branches from constraints
        {
            Expression e = constraints;
            while (e instanceof Operation && ((Operation) e).getOperator() == Operation.Operator.AND) {
                Operation op = (Operation) e;
                e = op.getOperand(0);
                Expression ee = op.getOperand(1);

                process(branches, ee);
            }

            process(branches, e);
        }

        // Send branches
        try {
            this.client.sendBranches(branches);
        } catch (IOException e) {
            throw new Error(e);
        }

        // Reset input
        this.input = null;
    }

    private void process(LinkedList<Coordinator.Branch> bs, Expression e) {
        Coverage.BranchData b = (Coverage.BranchData) e.metadata;

        if (b == null)
            return;

        Coordinator.Branch bb = new Coordinator.Branch();

        bb.takenID = b.takenCode;
        bb.notTakenID = b.notTakenCode;
        bb.result = b.taken;
        bb.controllingBytes = new HashSet<>();

        findControllingBytes(e, bb.controllingBytes);

        bs.add(bb);
    }

    private void findControllingBytes(Expression e, HashSet<Integer> bytes) {
        if (e instanceof Variable) {
            Variable v = (Variable) e;
            if (v.getName().startsWith("autoVar_")) {
                bytes.add(Integer.parseInt(v.getName().substring("autoVar_".length())));
            }
        } else if (e instanceof Operation) {
            Operation op = (Operation) e;
            for (int i = 0 ; i < op.getArity() ; i++)
                findControllingBytes(op.getOperand(i), bytes);
        }
    }

    @Override
    public Consumer<TraceEvent> generateCallBack(Thread thread) {
        return new Consumer<TraceEvent>() {
            @Override
            public void accept(TraceEvent traceEvent) {
            }
        };
    }

    private class TaintingInputStream extends InputStream {
        private final InputStream source;

        public TaintingInputStream(InputStream source) {
            this.source = source;
        }

        @Override
        public int read(byte[] b) throws IOException {
            if (b.length == 0)
                return 0;

            int ret = source.read(b);

            if (ret == -1)
                return ret;

            for (int i = 0 ; i < ret ; i++)
                b[i] = Symbolicator.symbolic(b[i]);

            return ret;
        }

        @Override
        public int read(byte[] b, int off, int len) throws IOException {
            if (len == 0)
                return 0;

            int ret = source.read(b, off, len);

            if (ret == -1)
                return ret;

            for (int i = off ; i < ret ; i++)
                b[i] = Symbolicator.symbolic(b[i]);

            return ret;
        }

        @Override
        public int read() throws IOException {
            int ret = source.read();

            return (ret == -1) ? ret : Symbolicator.symbolic((byte)ret);
        }
    }
}
