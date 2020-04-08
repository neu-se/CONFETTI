package edu.berkeley.cs.jqf.examples.microbench;

import com.pholser.junit.quickcheck.From;
import edu.berkeley.cs.jqf.examples.common.AsciiStringGenerator;
import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.*;
import java.nio.file.Files;
import java.util.Random;

@RunWith(JQF.class)
public class Microbenchmark {

    @Fuzz
    public void testWithInputStreamMagicNumberStatic(InputStream in) throws IOException {
//        if (in.read() == 100)
//            throw new Error("Found read magic value");
//
        DataInputStream dis = new DataInputStream(in);

//        if (dis.readChar() == 'a')
//            throw new Error("Found data char magic value");

//        if (dis.readByte() == 0x10)
//            throw new Error("Found data byte magic value");

        if (dis.readBoolean())
            throw new Error("Found data boolean magic value");

//        if (dis.readShort() == 150)
//            throw new Error("Found data short magic value");

        if (dis.readInt() == 1_500_000)
            throw new Error("Found data int magic value");

//        if (dis.readLong() == 5_500_000)
//            throw new Error("Found data long magic value");
    }

    @Fuzz
    public void testWithInputStreamMagicNumberDynamic(InputStream in) throws IOException {
        Random rnd = new Random();
        if (in.read() == rnd.nextInt(0xFFFF))
            throw new Error("Found read magic value");

//        DataInputStream dis = new DataInputStream(in);
//
//        if (dis.readChar() == rnd.nextInt(0xFFFF))
//            throw new Error("Found data char magic value");
//
//        if (dis.readByte() == rnd.nextInt(Byte.MAX_VALUE))
//            throw new Error("Found data byte magic value");
//
//        if (dis.readBoolean() == rnd.nextBoolean())
//            throw new Error("Found data boolean magic value");
//
//        if (dis.readShort() == rnd.nextInt(Short.MAX_VALUE))
//            throw new Error("Found data short magic value");
//
//        if (dis.readInt() == rnd.nextInt())
//            throw new Error("Found data int magic value");
//
//        if (dis.readLong() == rnd.nextLong())
//            throw new Error("Found data long magic value");
    }

    @Fuzz
    public void testWithInputStreamMagicStringStatic(InputStream in) throws IOException {
    }

    @Fuzz
    public void testWithInputStreamMagicStringStaticDynamic(InputStream in) throws IOException {
    }

    @Fuzz
    public void testWithInputStreamMagicStringDynamic(InputStream in) throws IOException {
    }

    @Fuzz
    public void testWithStringMagicStringStatic(@From(AsciiStringGenerator.class) String input) {
    }

    @Fuzz
    public void testWithStringMagicStringStaticDynamic(@From(AsciiStringGenerator.class) String input) {
    }

    @Fuzz
    public void testWithStringMagicStringDynamic(@From(AsciiStringGenerator.class) String input) {
    }

    @Fuzz
    public void testWithDictionaryStaticString(@From(AsciiStringGenerator.class) String input) {
    }

    @Fuzz
    public void testWithDictionaryStaticDynamicString(@From(AsciiStringGenerator.class) String input) {
    }

    @Fuzz
    public void testWithDictionaryDynamicString(@From(AsciiStringGenerator.class) String input) {
    }

    public static void main(String[] args) throws IOException {
        edu.berkeley.cs.jqf.examples.rhino.CompilerTest t = new edu.berkeley.cs.jqf.examples.rhino.CompilerTest();
        t.initContext();
        t.testWithString(new String(Files.readAllBytes(new File(args[0]).toPath())));
    }


}
