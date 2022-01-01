package edu.berkeley.cs.jqf.fuzz.guidance;

import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance;
import org.eclipse.collections.impl.list.mutable.primitive.ByteArrayList;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;

import java.io.*;
import java.nio.ByteBuffer;


public class RecordingInputStream extends InputStream {

    private final InputStream is;

    /*
    Track all of the bytes read
     */
    private final ByteArrayList bytesRead;
    /*
    Track the marks at which a new request starts
     */
    private final IntArrayList marks;
    private int pos = 0;


    private static ByteArrayList currentBuf; //WARNING NOT THREAD SAFE, NEED THIS IN GENERATORS :/
    private static IntArrayList currentMarks;
    public RecordingInputStream(InputStream is, ByteArrayList bytesReadBuffer, IntArrayList marksBuffer) {
        this.is = is;
        this.bytesRead = bytesReadBuffer;
        this.marks = marksBuffer;
        this.bytesRead.clear();
        this.marks.clear();
        currentBuf = this.bytesRead;
        currentMarks = this.marks;
    }

    public RecordingInputStream(InputStream is) {
        this(is, new ByteArrayList(ZestGuidance.MAX_INPUT_SIZE / 4), new IntArrayList(ZestGuidance.MAX_INPUT_SIZE / 16));
    }

    @Override
    public int read() throws IOException {
        int r = is.read();
        if (r != -1) {
            bytesRead.add((byte) r);
            marks.add(pos);
            pos++;
        }

        return r;
    }

    @Override
    public int read(byte[] b) throws IOException {
        int r = is.read(b);
        if (r != -1) {
            marks.add(pos);
            for(int i = 0; i < r; i++){
                bytesRead.add(b[i]);
            }
            pos += r;
        }
        return r;
    }

    @Override
    public int read(byte[] b, int off, int len) throws IOException {
        int r = is.read(b, off, len);
        if (len > 0 && r != -1) {
            marks.add(pos);
            for(int i = 0; i < r; i++){
                bytesRead.add(b[i]);
            }
            pos += r;
        }

        return r;
    }

    public MarkedInput getRecordedInput() {
        return new MarkedInput(bytesRead, marks);
    }

    public static void unsafePatchLastReadIntTo(int newVal){
        if (currentMarks != null && currentBuf != null) {
            //Did we in fact just read an int?
            int currentMark = currentMarks.getLast();
            if (currentBuf.size() - currentMark != 4) {
                throw new IllegalStateException("Expected to find a 4 byte int, but found " + (currentBuf.size() - currentMark));
            }
            byte[] tmp = new byte[4];
            ByteBuffer.wrap(tmp).putInt(newVal);
            for (int i = 0; i < 4; i++) {
                currentBuf.set(currentMark + i, tmp[i]);
            }
        }
    }
    public static int unsafeGetLastMark(){
        if(currentMarks == null)
            return 0;
        return currentMarks.getLast();
    }

    public static class MarkedInput implements Externalizable {
        private byte[] bytesRead;
        private int[] marks;

        public MarkedInput(){

        }

        protected MarkedInput(ByteArrayList bytesRead, IntArrayList marks){
            this.bytesRead = bytesRead.toArray();
            this.marks = marks.toArray();
        }

        @Override
        public void writeExternal(ObjectOutput out) throws IOException {
            out.writeInt(bytesRead.length);
            out.write(bytesRead);
            out.writeInt(marks.length);
            for(int i = 0; i < marks.length; i++){
                out.writeInt(marks[i]);
            }
        }

        public byte[] getBytesRead() {
            return bytesRead;
        }

        public int[] getMarks() {
            return marks;
        }

        /**
         * Returns the length of this request. That is: for an INDEX of a mark, tell us how long in the bytes array it spans
         * @param markIndex
         * @return
         */
        public int getMarkLength(int markIndex){
            if (markIndex == marks.length - 1) {
                return bytesRead.length - marks[markIndex]; //if last mark, the length of the read is the remaining length of the array
            } else {
                //else it's the distance to the next mark
                return marks[markIndex+1] - marks[markIndex];
            }
        }

        @Override
        public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
            this.bytesRead = new byte[in.readInt()];
            in.readFully(this.bytesRead);
            this.marks = new int[in.readInt()];
            for(int i = 0; i < this.marks.length; i++){
                this.marks[i] = in.readInt();
            }
        }
    }
}
