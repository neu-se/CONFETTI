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

    public static void examineAllStrCombinations(MagicInput input){
        ////Compare 2 concated symbolic strings to a concrete string
        String testStr = input.str.concat(input.str2);
        if(testStr.equals("abcdefghijklmnopqqrstuvwxyz")){
            throw new StringIndexOutOfBoundsException("Found it1!");
        }

        //Compare concrete string to 2 concated strings
        testStr = input.str.concat(input.str2);
        if("1234596789".equals(testStr)){
            throw new StringIndexOutOfBoundsException("Found it2!");
        }

        //Compare 2 concated symbolic strings to a symbolic string
        if(input.str.concat(input.str2).equals(input.str3)){
            throw new StringIndexOutOfBoundsException("Found it3!");
        }

        //Compare symbolic+concrete to concrete
        if(input.str.concat("abcd").equals("dabcd")){
            throw new StringIndexOutOfBoundsException("Found it4!");
        }

        //Compare concrete+symbolic to concrete
        if("abcd".concat(input.str).equals("abcdefghijklmno")){
            throw new StringIndexOutOfBoundsException("Found it5!");
        }

        //Compare symbolic+concrete to symbolic
        if(input.str.equals("abc") && input.str.concat("z").equals(input.str2)){
            throw new StringIndexOutOfBoundsException("Found it6!");
        }

        //Compare symbolic+concrete to symbolic+concrete
        if(input.str2.startsWith("r") && input.str.concat("z").equals(input.str2.concat("az"))){
            throw new StringIndexOutOfBoundsException("Found it6!");
        }

        ////Compare concrete+symbolic to symbolic+concrete
        if("ab".concat(input.str).equals(input.str2.concat("bcd"))){
            throw new StringIndexOutOfBoundsException("Found it7!");
        }

        //TODO these are not supported right now.
        //if(input.str.indexOf('!') == 0 && input.str.endsWith("!ao")){
        //    throw new StringIndexOutOfBoundsException("Found it 8!");
        //}
        //if(input.str.length() == 5 && input.str.startsWith("R*R")){
        //    throw new StringIndexOutOfBoundsException("Found it9!");
        //}
    }

    public static void examineInputStringOnly(MagicInput input) {
        String str3 = input.str.concat(input.str2);
        if (str3.equals("hello world!")) {
            throw new StringIndexOutOfBoundsException("Ah you found it!");
        }
        String str4 = input.str.concat("ORLD!");
        if(str4.equals("HELLO WORLD!")){
            //TODO get this one, too!
            throw new StringIndexOutOfBoundsException("You found the second one!");
        }
    }
    public static void examineInputStringOnlyDoubleSymbolic(MagicInput input) {
        String str3 = input.str.concat("World!");
        if (str3.equals(input.str2)) {
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
        public String str3;

        @Override
        public String toString() {
            return "MagicInput{" +
                    "str='" + str + '\'' +
                    ", str2='" + str2 + '\'' +
                    ", str3='" + str3 + '\'' +
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
            ret.str3 = stringGenerator.generate(random, status);
            ret.i2 = random.nextInt();
            return ret;
        }
    }
}
