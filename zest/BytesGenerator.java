import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance;
import edu.gmu.swe.knarr.runtime.TaintListener;

import java.lang.reflect.Field;

public class BytesGenerator extends Generator<byte[]> {
    public static final int SIZE;

    static {
        SIZE = 1 << Integer.parseInt(System.getProperty("size","10"));

        // Set max random data size
        ZestGuidance.MAX_INPUT_SIZE = SIZE * Byte.SIZE;

        // Disable Knarr optimization to ignore large arrays
        TaintListener.IGNORE_LARGE_ARRAY_SIZE = SIZE;
        TaintListener.IGNORE_LARGE_ARRAY_INDEX = SIZE;
    }

    public BytesGenerator() {
        super(byte[].class);
    }

    @Override
    public byte[] generate(SourceOfRandomness random, GenerationStatus __ignore__) {
        byte[] ret = new byte[SIZE];

        for (int i = 0 ; i < SIZE ; i++)
            ret[i] = random.nextByte(Byte.MIN_VALUE, Byte.MAX_VALUE);

        return ret;
    }
}
