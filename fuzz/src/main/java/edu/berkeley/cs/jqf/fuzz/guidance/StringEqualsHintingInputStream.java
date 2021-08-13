package edu.berkeley.cs.jqf.fuzz.guidance;

import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance;

import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;

public class StringEqualsHintingInputStream extends InputStream {

    private final InputStream is;
    private final LinkedList<int[]> reqs;
    private final LinkedList<Coordinator.StringHint[]> hints;
    private final RecordingInputStream ris;

    private int offset = 0;
    private int[] curReqs;
    private Coordinator.StringHint[] curHints;


    private static Coordinator.StringHint[] EMPTY = new Coordinator.StringHint[0];
    private static Coordinator.StringHint[] hintsForCurrentInput = EMPTY;

    public static Boolean hintUsedInCurrentInput = false;
    public static Boolean z3HintsUsedInCurrentInput = false;

    private static LinkedList<Coordinator.StringHint[]> globalHints;

    private static LinkedList<Coordinator.StringHint[]> aggregatedHints =  new LinkedList<>();

    public static Coordinator.StringHint[] getHintsForCurrentInput() {
        Coordinator.StringHint[] ret = hintsForCurrentInput;
        hintsForCurrentInput = EMPTY;
        return ret;
    }

    public StringEqualsHintingInputStream(InputStream is, RecordingInputStream ris, ZestGuidance.Input input) {
        this.is = is;
        this.reqs = new LinkedList<>(input.instructions);
        this.hints = new LinkedList<>(input.stringEqualsHints);
        this.ris = ris;

        globalHints = new LinkedList<>(hints);
        aggregatedHints = new LinkedList<>();

        if (this.reqs.size() != this.hints.size())
            throw new IllegalStateException();

        if (!this.reqs.isEmpty()) {
            curReqs = this.reqs.removeFirst();
            curHints = this.hints.removeFirst();
        }

    }

    public static LinkedList<Coordinator.StringHint[]> getHints() {
        // return hintsCopy;
        return aggregatedHints;
    }

    private int setHints(int read) {

        if (read <= 0 || this.reqs == null || this.curReqs == null)
            return read;

        if (offset >= curReqs[0] && offset < curReqs[0] + curReqs[1]) {
            if (curHints.length > 0)
                hintsForCurrentInput = curHints;
            else
                hintsForCurrentInput = EMPTY;

            aggregatedHints.addLast(hintsForCurrentInput);
            offset += read;
        } else if (offset < curReqs[0]) {
            offset += read;
        } else if (offset >= curReqs[0] + curReqs[1] && !reqs.isEmpty()) {
            curReqs = reqs.removeFirst();
            curHints = hints.removeFirst();
            offset += read;
            return setHints(read);
        } else {
            curReqs = null;
            curHints = null;
            offset += read;
        }

        return read;
    }

    @Override
    public int read() throws IOException {
        int ret = is.read();
        setHints(ret == -1 ? 0 : 1);
        return ret;
    }

    @Override
    public int read(byte[] b) throws IOException {
        return setHints(is.read(b));
    }

    @Override
    public int read(byte[] b, int off, int len) throws IOException {
        return setHints(is.read(b, off, len));
    }
}
