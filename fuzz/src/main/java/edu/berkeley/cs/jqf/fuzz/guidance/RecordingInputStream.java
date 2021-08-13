package edu.berkeley.cs.jqf.fuzz.guidance;

import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;

public class RecordingInputStream extends InputStream {

    private final InputStream is;
    protected LinkedList<byte[]> reqs = new LinkedList<>();

    public RecordingInputStream(InputStream is) {
        this.is = is;
        lastReadOffset = 0;
        lastReadBytes = null;
    }

    @Override
    public int read() throws IOException {
        int r = is.read();
        if (r != -1) {
            lastReadOffset++;
            reqs.addLast(new byte[]{(byte) r});
        }

        return r;
    }

    @Override
    public int read(byte[] b) throws IOException {
        int r = is.read(b);
        if (r != -1) {
            lastReadOffset += r;
            byte[] bb = new byte[r];
            System.arraycopy(b, 0, bb, 0, r);
            reqs.addLast(bb);
        }

        return r;
    }

    public static byte[] lastReadBytes;
    public static int lastReadOffset;
    @Override
    public int read(byte[] b, int off, int len) throws IOException {
        int r = is.read(b, off, len);
        if (len > 0 && r != -1) {
            lastReadOffset += r;
            byte[] bb = new byte[r];
            System.arraycopy(b, 0, bb, 0, r);
            lastReadBytes = bb;
            reqs.addLast(bb);
        }

        return r;
    }

    public LinkedList<byte[]> getRequests() {
        return this.reqs;
    }
}
