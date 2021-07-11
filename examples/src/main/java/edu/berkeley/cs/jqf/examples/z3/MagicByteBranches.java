package edu.berkeley.cs.jqf.examples.z3;

import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import edu.berkeley.cs.jqf.examples.common.AlphaStringGenerator;
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

    public static void examineInputStringOnlyCharAt(MagicInput input){
        if(input.str2.charAt(0) == '!') {
            if (input.str.charAt(0) == ':') {
                throw new StringIndexOutOfBoundsException("You found it!");
            }
        }
    }
    public static void examineInputCharAt(MagicInput input){
        if(input.i1 == 49505) {
            if (input.str2.charAt(0) == '!') {
                if(input.i2 < -1857490347) {
                    if (input.str.charAt(0) == ':') {
                        throw new StringIndexOutOfBoundsException("You found it!");
                    }
                }
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

        @Override
        public String toString() {
            return "MagicInput{" +
                    "str='" + str + '\'' +
                    ", str2='" + str2 + '\'' +
                    ", i1=" + i1 +
                    ", i2=" + i2 +
                    '}';
        }

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
                stringGenerator = new DictionaryBackedStringGenerator(dict.value(), new AlphaStringGenerator());
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
