package edu.berkeley.cs.jqf.examples.z3;

import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import edu.berkeley.cs.jqf.examples.common.AsciiStringGenerator;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.examples.common.DictionaryBackedStringGenerator;

import java.io.IOException;

public class MagicByteBranches {
    public static void examineInputNestedStringFirst(MagicInput input) {
        String str3 = input.str.concat(input.str2);
        if (str3.equals("hello world!")) {
            if (input.i1 == 99) {
                if (input.i2 == 495830) {
                    throw new StringIndexOutOfBoundsException("Ah you found it!");
                }
            }
        }
    }

    public static void examineInputIntsOnly(MagicInput input) {
        if (input.i1 == 99) {
            if (input.i2 == 495830) {
                throw new StringIndexOutOfBoundsException("Ah you found it!");
            }
        }
    }

    public static void examineInputStringOnly(MagicInput input) {
        String str3 = input.str.concat(input.str2);
        if (str3.equals("hello world!")) {
            throw new StringIndexOutOfBoundsException("Ah you found it!");
        }
    }

    public static void examineInputIntFirst(MagicInput input) {
        if(input.i1 == 99){
            String str3 = input.str.concat(input.str2);
            if (str3.equals("hello world!")) {
                throw new StringIndexOutOfBoundsException("Ah you found it!");
            }
        }
    }


    public static class MagicInput {
        public String str;
        public String str2;
        public int i1;
        public int i2;

    }

    public static class MagicInputGenerator extends Generator<MagicInput> {

        private DictionaryBackedStringGenerator stringGenerator;
        public MagicInputGenerator() {
            super(MagicInput.class);
        }

        public void configure(Dictionary dict) {
            try {
                stringGenerator = new DictionaryBackedStringGenerator(dict.value(), new AsciiStringGenerator());
            } catch (IOException e) {
                e.printStackTrace();
            }
        }

        @Override
        public MagicInput generate(SourceOfRandomness random, GenerationStatus status) {
            MagicInput ret = new MagicInput();
            ret.i1 = random.nextInt();
            ret.str = stringGenerator.generate(random, status);
            ret.str2 = stringGenerator.generate(random, status);
            ret.i2 = random.nextInt();
            return ret;
        }
    }
}
