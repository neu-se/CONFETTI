package edu.berkeley.cs.jqf.fuzz.knarr;

import edu.berkeley.cs.jqf.fuzz.central.KnarrClient;
import edu.berkeley.cs.jqf.fuzz.guidance.Guidance;
import edu.berkeley.cs.jqf.fuzz.guidance.GuidanceException;
import edu.berkeley.cs.jqf.fuzz.guidance.Result;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEvent;
import edu.gmu.swe.knarr.runtime.PathUtils;
import edu.gmu.swe.knarr.runtime.Symbolicator;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.Operation;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
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
    public void setArgs(Object[] args) {
    }

    @Override
    public void handleResult(Result result, Throwable error) throws GuidanceException {

        System.out.println(result);

        LinkedList<Expression> constraints = new LinkedList<>();

        // Turn constraints into list
        {
            Expression exp = PathUtils.getCurPC().constraints;
            while (exp instanceof Operation && ((Operation) exp).getOperator() == Operation.Operator.AND) {
                Operation op = (Operation) exp;
                exp = op.getOperand(0);
                Expression e = op.getOperand(1);

                constraints.addLast(e);
            }

            constraints.addLast(exp);
        }

        // Send constraints
        try {
            this.client.sendConstraints(constraints);
        } catch (IOException e) {
            throw new Error(e);
        }

        // Reset input
        this.input = null;
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
