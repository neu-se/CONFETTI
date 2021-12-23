package edu.berkeley.cs.jqf.fuzz.knarr;

import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.central.KnarrClient;
import edu.berkeley.cs.jqf.fuzz.central.KnarrWorker;
import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance;
import edu.berkeley.cs.jqf.fuzz.guidance.Guidance;
import edu.berkeley.cs.jqf.fuzz.guidance.GuidanceException;
import edu.berkeley.cs.jqf.fuzz.guidance.Result;
import edu.berkeley.cs.jqf.fuzz.guidance.StringEqualsHintingInputStream;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEvent;
import edu.columbia.cs.psl.phosphor.struct.TaintedWithObjTag;
import edu.gmu.swe.knarr.runtime.PathUtils;
import edu.gmu.swe.knarr.runtime.StringUtils;
import edu.gmu.swe.knarr.runtime.Symbolicator;
import za.ac.sun.cs.green.expr.*;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.*;
import java.util.function.Consumer;

public class KnarrGuidance implements Guidance {
    private Coordinator.Input input;
    private KnarrClient client;
    private TaintingInputStream currentTaintingInputStream;

    public KnarrGuidance() throws IOException  {
        this.client = new KnarrClient();
    }

    public static class InputWithOnlyHints extends ZestGuidance.Input{

        @Override
        public int getOrGenerateFresh(Object key, Random random) {
            throw new UnsupportedOperationException();
        }

        @Override
        public int size() {
            throw new UnsupportedOperationException();
        }

        @Override
        public ZestGuidance.Input fuzz(Random random) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void gc() {
            throw new UnsupportedOperationException();
        }

    }

    public static HashMap<String, String> generatedStrings = new HashMap<>();
    @Override
    public InputStream getInput() throws IllegalStateException, GuidanceException {
        Symbolicator.reset();
        generatedStrings.clear();
        ZestGuidance.Input zestInput = new InputWithOnlyHints();
        zestInput.instructions = input.instructions;
        zestInput.stringEqualsHints = input.hints;
        zestInput.appliedTargetedHints = new LinkedList<>(input.targetedHints);
        this.currentTaintingInputStream =  new TaintingInputStream(new StringEqualsHintingInputStream(new ByteArrayInputStream(this.input.bytes), null, zestInput));
        return this.currentTaintingInputStream;
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
        // Generation is done. Check and record all constraints that have ocurred so far.
        // Any bytes that were used NOW were used in control decisions IN THE GENERATOR,
        // and hence are likely to control *structural* elements of the input, rather than
        // specific values through data flow (like string hints do)
        Expression constraints = PathUtils.getCurPC().constraints;
        HashSet<Integer> choiceVars = extractVarNames(constraints);
        LinkedList<int[]> rangesUsedInControlPointsInGenerator = new LinkedList<>();

        for(int[] requestForRandomBytes : this.currentTaintingInputStream.readRequests){
            boolean fullRequestMatched = false;
            int offsetsMatched = 0;
            if(requestForRandomBytes[1] != 1)
                continue; //TODO testing with only booleans
            for(int i = requestForRandomBytes[0]; i< requestForRandomBytes[0] + requestForRandomBytes[1]; i++){
                if(choiceVars.contains(i)){
                    offsetsMatched++;
                }
            }
            if(offsetsMatched == requestForRandomBytes[1]){
                // The entire request matched
                rangesUsedInControlPointsInGenerator.add(requestForRandomBytes);
            }else{
                // Only part of the request matched, add each byte one-by-one
                for(int i = requestForRandomBytes[0]; i< requestForRandomBytes[0] + requestForRandomBytes[1]; i++){
                    if (choiceVars.contains(i)) {
                        rangesUsedInControlPointsInGenerator.add(new int[]{i, 1});
                    }
                }
            }
        }
        //for (int[] each : rangesUsedInControlPointsInGenerator) {
        //    System.out.println("TARGET: " + each[0] + "..." + (each[0] + each[1]));
        //}
    }
    public static HashSet<Integer> extractVarNames(Expression exp) {
        LinkedList<Expression> toVisit = new LinkedList<>();
        toVisit.add(exp);
        HashSet<Integer> ret = new HashSet<>();
        while (!toVisit.isEmpty()) {
            Expression each = toVisit.pop();
            if (each instanceof BinaryOperation) {
                toVisit.add(((BinaryOperation) each).getOperand(0));
                toVisit.add(((BinaryOperation) each).getOperand(1));
            } else if (each instanceof UnaryOperation) {
                toVisit.add(((UnaryOperation) each).getOperand(0));
            } else if (each instanceof NaryOperation) {
                for (Expression operand : ((NaryOperation) each).getOperands()) {
                    toVisit.add(operand);
                }
            } else if (each instanceof Variable) {
                String name = ((Variable) each).getName();
                if(name.startsWith("autoVar_")){
                    ret.add(Integer.valueOf(name.substring("autoVar_".length())));
                }
                //} else if (each instanceof FunctionCall) {
                //    ret.add(((FunctionCall) each).getName());
            }
        }
        return ret;
    }


    public static HashSet<String> extractChoices(Expression exp) {
        LinkedList<Expression> toVisit = new LinkedList<>();
        toVisit.add(exp);
        HashSet<String> ret = new HashSet<>();
        while (!toVisit.isEmpty()) {
            Expression each = toVisit.pop();
            if (each instanceof BinaryOperation) {
                toVisit.add(((BinaryOperation) each).getOperand(0));
                toVisit.add(((BinaryOperation) each).getOperand(1));
            } else if (each instanceof UnaryOperation) {
                toVisit.add(((UnaryOperation) each).getOperand(0));
            } else if (each instanceof NaryOperation) {
                for (Expression operand : ((NaryOperation) each).getOperands()) {
                    toVisit.add(operand);
                }
            } else if (each instanceof Variable) {
                String name = ((Variable) each).getName();
                if(name.startsWith("autoVar_")){
                    ret.add(name);
                }
            } else if (each instanceof FunctionCall) {
                ret.add(((FunctionCall) each).toString());
            }
        }
        return ret;
    }

    public static void printOutStringHints(){
        LinkedList<Expression> constraints = new LinkedList<>();

        // Turn constraints into list
        {
            Expression exp = PathUtils.getCurPC().constraints;
            while (exp instanceof Operation && ((Operation) exp).getOperator() == Operation.Operator.AND) {
                Operation op = (Operation) exp;
                exp = op.getOperand(0);
                Expression e = op.getOperand(1);

                constraints.addFirst(e);
            }

            constraints.addFirst(exp);
        }

    }
    @Override
    public void handleResult(Result result, Throwable error) throws GuidanceException {

        //printOutStringHints();
        //System.out.println("#"+ this.input.id + " " + result + "(Expected: "+this.input.isValid+")");
        if(result == Result.INVALID && this.input.isValid){
            error.printStackTrace();
        }

        LinkedList<Expression> constraints = new LinkedList<>();

        // Turn constraints into list
        {
            Expression exp = PathUtils.getCurPC().constraints;
            while (exp instanceof Operation && ((Operation) exp).getOperator() == Operation.Operator.AND) {
                Operation op = (Operation) exp;
                exp = op.getOperand(0);
                Expression e = op.getOperand(1);
                constraints.addFirst(e);
            }

            constraints.addFirst(exp);
        }

        // DEBUG strategy: look at hints in knarr process
        //LinkedList<Coordinator.Branch> bs = new LinkedList<>();
        //HashMap<Integer, HashSet<Coordinator.StringHint>> eqs = new HashMap<>();
        //HashSet<Integer> bytesUsedBySUT = new HashSet<>();
        //for (Expression e : constraints)
        //    KnarrWorker.process(bs, eqs, e, bytesUsedBySUT, new String[0]);

        // END DEBUG help

        // Send constraints
        try {
            this.client.sendConstraints(this.input.id, constraints, new HashMap<>(generatedStrings));
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

    public static class TaintingInputStream extends InputStream {
        private final InputStream source;

        private int totalBytesRead;

        /*
        Track which input bytes were read in the same request, so if we want to target fuzzing to some bytes,
        we can group that targetting to a single request (e.g. reading a boolean vs reading a long)
         */
        public LinkedList<int[]> readRequests = new LinkedList<>();

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

            readRequests.add(new int[]{totalBytesRead, ret}); //Record the offset we read at, and the length
            for (int i = 0 ; i < ret ; i++){
                b[i] = Symbolicator.symbolic(b[i]);
            }

            totalBytesRead += ret;
            return ret;
        }

        @Override
        public int read(byte[] b, int off, int len) throws IOException {
            if (len == 0)
                return 0;

            int ret = source.read(b, off, len);

            if (ret == -1)
                return ret;

            readRequests.add(new int[]{totalBytesRead, ret}); //Record the offset we read at, and the length
            for (int i = off ; i < ret ; i++)
                b[i] = Symbolicator.symbolic(b[i]);

            totalBytesRead += ret;

            return ret;
        }

        @Override
        public int read() throws IOException {
            int ret = source.read();
            if(ret == -1)
                return ret;

            readRequests.add(new int[]{totalBytesRead, 1}); //Record the offset we read at, and the length
            ret = Symbolicator.symbolic((byte)ret);

            totalBytesRead++;
            return ret;
        }
    }
}
