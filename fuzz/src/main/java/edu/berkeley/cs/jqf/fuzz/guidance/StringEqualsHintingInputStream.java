package edu.berkeley.cs.jqf.fuzz.guidance;

import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;

public class StringEqualsHintingInputStream extends InputStream {

    private final InputStream is;
    private final LinkedList<int[]> reqs;
    private final LinkedList<String[]> hints;

    private int offset = 0;
    private int[] curReqs;
    private String[] curHints;

    private static String[] EMPTY = new String[0];
    private static String[] hintsForCurrentInput = EMPTY;

    public static String[] getHintsForCurrentInput() {
        return hintsForCurrentInput;
    }

    public StringEqualsHintingInputStream(InputStream is, LinkedList<int[]> reqs, LinkedList<String[]> hints) {
        this.is = is;
        this.reqs = reqs;
        this.hints = hints;

        if (reqs.size() != hints.size())
            throw new IllegalStateException();

        if (!reqs.isEmpty()) {
            curReqs = reqs.removeFirst();
            curHints = hints.removeFirst();
        }
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
