package edu.berkeley.cs.jqf.fuzz.guidance;

import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.central.Z3InputHints;

import java.io.IOException;
import java.io.InputStream;
import java.util.*;

public class StringEqualsHintingInputStream extends InputStream {

    private final InputStream is;
    private final LinkedList<int[]> reqs;
    private final LinkedList<Coordinator.StringHint[]> hints;

    private int offset = 0;
    private int[] curReqs;
    private Coordinator.StringHint[] curHints;

    private static Coordinator.StringHint[] EMPTY = new Coordinator.StringHint[0];
    private static Coordinator.StringHint[] hintsForCurrentInput = EMPTY;

    public static Boolean hintUsedInCurrentInput = false;
    public static Boolean z3HintsUsedInCurrentInput = false;

    private static LinkedList<Coordinator.StringHint[]> globalHints;
    private static LinkedList<Coordinator.StringHint[]> hintsCopy;


    public static Coordinator.StringHint[] getHintsForCurrentInput() {
        Coordinator.StringHint[] ret = hintsForCurrentInput;
        hintsForCurrentInput = EMPTY;
        return ret;
    }


    public static Coordinator.StringHint[] getHintsForCurrentInputGlobal() {

        if(globalHints == null || globalHints.isEmpty())
            return EMPTY;
        else
            return globalHints.removeFirst();

    }


    // This will only be called in the Knarr process - we use this class to hold the hints.
    public StringEqualsHintingInputStream(LinkedList<Coordinator.StringHint[]> hints) {
        this.hints = hints;
        this.is = null;
        this.reqs = null;
        globalHints = new LinkedList<>(hints);
        hintsCopy = new LinkedList<>(hints);
    }

    public StringEqualsHintingInputStream(InputStream is, LinkedList<int[]> reqs, LinkedList<Coordinator.StringHint[]> hints) {
        this.is = is;
        this.reqs = reqs;
        this.hints = hints;

        globalHints = new LinkedList<>(hints);
        hintsCopy = new LinkedList<>(hints);


        if (reqs.size() != hints.size())
            throw new IllegalStateException();

        if (!reqs.isEmpty()) {
            curReqs = reqs.removeFirst();
            curHints = hints.removeFirst();
        }

    }

    public static LinkedList<Coordinator.StringHint[]> getHints() {
        return hintsCopy;
    }

    private int setHints(int read) {

        if (read <= 0 || this.reqs == null || this.curReqs == null)
            return read;

        if (offset >= curReqs[0] && offset < curReqs[0] + curReqs[1]) {
            if (curHints.length > 0)
                hintsForCurrentInput = curHints;
            else
                hintsForCurrentInput = EMPTY;
            offset += read;
        } else if (offset < curReqs[0]) {
            offset += read;
        } else if (offset >= curReqs[0] + curReqs[1] && !reqs.isEmpty()) {
            curReqs = reqs.removeFirst();
            curHints = hints.removeFirst();
            return setHints(read);
        } else {
            curReqs = null;
            curHints = null;
        }

        return read;
    }

    @Override
    public int read() throws IOException {
        return setHints(is.read());
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
