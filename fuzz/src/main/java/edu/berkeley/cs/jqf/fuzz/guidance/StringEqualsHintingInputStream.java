package edu.berkeley.cs.jqf.fuzz.guidance;

import edu.berkeley.cs.jqf.fuzz.central.Z3InputHints;

import java.io.IOException;
import java.io.InputStream;
import java.util.*;

public class StringEqualsHintingInputStream extends InputStream {

    private final InputStream is;
    private final LinkedList<int[]> reqs;
    private final LinkedList<String[]> hints;
    private final LinkedList<Z3InputHints.Z3StringHint> z3Hints;

    private int offset = 0;
    private int[] curReqs;
    private String[] curHints;

    private static String[] EMPTY = new String[0];
    private static String[] hintsForCurrentInput = EMPTY;

    public static Boolean hintUsedInCurrentInput = false;

    private static LinkedList<String[]> globalHints;
    private static LinkedList<String[]> hintsCopy;

    private static LinkedList<Z3InputHints.Z3StringHint> z3HintsCopy;

    public static String[] getHintsForCurrentInput() {
        String[] ret = hintsForCurrentInput;
        hintsForCurrentInput = EMPTY;
        return ret;
    }

    public static String[] getHintsForGeneratorFunction(String genFunc) {
        if(z3HintsCopy == null) return null;

        ArrayList<String> ret = new ArrayList<>();

        for(Z3InputHints.Z3StringHint z3StringHint: z3HintsCopy) {

            if(z3StringHint.getHint().getKey().equals(genFunc)) {
                ret.add(z3StringHint.getHint().getValue());
            }

        }
        if(ret.size() == 0) return null;
        else return ret.toArray(new String[0]);

    }


    public static String[] getHintsForCurrentInputGlobal() {

        if(globalHints == null || globalHints.isEmpty())
            return EMPTY;
        else
            return globalHints.removeFirst();

    }


    // This will only be called in the Knarr process - we use this class to hold the hints.
    public StringEqualsHintingInputStream(LinkedList<String[]> hints) {
        this.hints = hints;
        this.z3Hints = new LinkedList<Z3InputHints.Z3StringHint>();
        this.is = null;
        this.reqs = null;
        globalHints = new LinkedList<>(hints);
        hintsCopy = new LinkedList<>(hints);
        z3HintsCopy = new LinkedList<>();
    }

    public StringEqualsHintingInputStream(InputStream is, LinkedList<int[]> reqs, LinkedList<String[]> hints, LinkedList<Z3InputHints.Z3StringHint> z3Hints) {
        this.is = is;
        this.reqs = reqs;
        this.hints = hints;
        this.z3Hints = z3Hints;

        globalHints = new LinkedList<>(hints);
        hintsCopy = new LinkedList<>(hints);
        z3HintsCopy = new LinkedList<>(z3Hints);


        if (reqs.size() != hints.size())
            throw new IllegalStateException();

        if (!reqs.isEmpty()) {
            curReqs = reqs.removeFirst();
            curHints = hints.removeFirst();
        }

    }

    public static LinkedList<String[]> getHints() {
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
