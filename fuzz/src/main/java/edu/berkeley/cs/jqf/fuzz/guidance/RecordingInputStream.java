package edu.berkeley.cs.jqf.fuzz.guidance;

import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;

public class RecordingInputStream extends InputStream {

    private final InputStream is;
    private LinkedList<byte[]> reqs = new LinkedList<>();

    public RecordingInputStream(InputStream is) {
        this.is = is;
    }

    @Override
    public int read() throws IOException {
        int r = is.read();
        if (r != -1)
            reqs.addLast(new byte[]{(byte)r});

        return r;
    }

    @Override
    public int read(byte[] b) throws IOException {
        int r = is.read(b);
        if (r != -1) {
            byte[] bb = new byte[r];
            System.arraycopy(b, 0, bb, 0, r);
            reqs.addLast(bb);
        }

        return r;
    }

    @Override
    public int read(byte[] b, int off, int len) throws IOException {
        int r = is.read(b, off, len);
        if (len > 0 && r != -1) {
            byte[] bb = new byte[r];
            System.arraycopy(b, 0, bb, 0, r);
            reqs.addLast(bb);
        }

        return r;
    }

    public LinkedList<byte[]> getRequests() {
        return this.reqs;
    }
}
