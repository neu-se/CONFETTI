package edu.berkeley.cs.jqf.examples.microbench;

import com.pholser.junit.quickcheck.From;
import edu.berkeley.cs.jqf.examples.common.AsciiStringGenerator;
import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.guidance.StringEqualsHintingInputStream;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.*;

@RunWith(JQF.class)
public class Microbenchmark {

    private int getInt(InputStream in) throws IOException {
        return ((in.read() & 0xFF) << 24) |
               ((in.read() & 0xFF) << 16) |
               ((in.read() & 0xFF) << 8 ) |
               ((in.read() & 0xFF) << 0 );
    }

    @Fuzz
    public void testWithInputStreamMagicNumberStatic(InputStream in) throws IOException {

        for (int i = 0 ; i < 100 ; i++)
            in.read();

        if (in.read() == 100)
            throw new Error("Found read byte magic value");

        if ((in.read() % 2) == 0)
            throw new Error("Found read boolean magic value");

        if (getInt(in) == 1_500_000)
            throw new Error("Found read int magic value");

        DataInputStream dis = new DataInputStream(in);

        if (dis.readChar() == 'a')
            throw new Error("Found data char magic value");

        if (dis.readByte() == 0x10)
            throw new Error("Found data byte magic value");

        if (dis.readBoolean())
            throw new Error("Found data boolean magic value");

        if (dis.readShort() == 150)
            throw new Error("Found data short magic value");

        if (dis.readInt() == 1_500_000)
            throw new Error("Found data int magic value");

        if (dis.readLong() == 5_500_000)
            throw new Error("Found data long magic value");
    }

    @Fuzz
    public void testWithInputStreamMagicNumberDynamic(InputStream in) throws IOException {
        // TODO add unused data between two consecutive reads

        {
            int i1 = getInt(in);
            int i2 = getInt(in);
            if (i1 != 0 && i2 != 0 && i1 == i2)
                throw new Error("Found read int magic value: " + i1 + " : " + i2);
        }

        {
            int i1 = getInt(in);
            int i2 = getInt(in);
            if (i1 > 1000 && i2 > 3000 && i1 == i2)
                throw new Error("Found read int magic value: " + i1 + " : " + i2);
        }

        DataInputStream dis = new DataInputStream(in);

        if (dis.readChar() == (dis.readChar() + 10))
            throw new Error("Found data char magic value");

        if (dis.readByte() == (dis.readByte() & 0xDA))
            throw new Error("Found data byte magic value");

        if (dis.readBoolean() == !dis.readBoolean())
            throw new Error("Found data boolean magic value");

        {
            short s1 = dis.readShort();
            short s2 = dis.readShort();
            if (s1 != 0 && s2 != 0 && s1 == s2)
                throw new Error("Found data short magic value: " + s1 + " : " + s2);
        }

        {
            int i1 = dis.readInt();
            int i2 = dis.readInt();
            if (i1 != 0 && i2 != 0 && i1 == i2)
                throw new Error("Found data int magic value: " + i1 + " : " + i2);
        }

        {
            long l1 = dis.readLong();
            long l2 = dis.readLong();
            if (l1 != 0 && l2 != 0 && l1 == l2)
                throw new Error("Found data long magic value: " + l1 + " : " + l2);
        }
    }

    private String generateString(InputStream in, boolean useHints) throws IOException {
        byte[] bytes = new byte[100];
        in.read(bytes);

        String gen = new String(bytes);

        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();

        //if (hints != null && hints.length > 0 && (coin < 90)) {


        if (hints != null && hints.length > 0) {


            int choice = getInt(in) % hints.length;
            gen = hints[choice].getHint();

        }

        return gen;
    }

        @Fuzz
    public void testWithInputStreamMagicStringStatic(InputStream in) throws IOException {
        if ("test".equals(generateString(in, true)))
            throw new Error("Found read magic string using hints");

        if ("test".equals(generateString(in, false)))
            throw new Error("Found read magic string ");

        switch (generateString(in, true)) {
            case "case1":
                throw new Error("Found switch read magic string 1 using hints");
            case "2":
                throw new Error("Found switch read magic string 2 using hints");
            case "big string case 4":
                throw new Error("Found switch read magic string 3 using hints");
        }

        switch (generateString(in, false)) {
            case "case1":
                throw new Error("Found switch read magic string 1");
            case "2":
                throw new Error("Found switch read magic string 2");
            case "big string case 4":
                throw new Error("Found switch read magic string 3");
        }
    }

    @Fuzz
    public void testWithInputStreamMagicStringDynamic(InputStream in) throws IOException {
        if (generateString(in, true).equals(generateString(in, true)))
            throw new Error("Found read magic string using hints");

        if (generateString(in, false).equals(generateString(in, false)))
            throw new Error("Found read magic string using hints");
    }

//    @Fuzz
//    public void testWithStringMagicStringStatic(@From(AsciiStringGenerator.class) String input) {
//    }
//
//    @Fuzz
//    public void testWithStringMagicStringStaticDynamic(@From(AsciiStringGenerator.class) String input) {
//    }
//
//    @Fuzz
//    public void testWithStringMagicStringDynamic(@From(AsciiStringGenerator.class) String input) {
//    }
//
//    @Fuzz
//    public void testWithDictionaryStaticString(@From(AsciiStringGenerator.class) String input) {
//    }
//
//    @Fuzz
//    public void testWithDictionaryStaticDynamicString(@From(AsciiStringGenerator.class) String input) {
//    }
//
//    @Fuzz
//    public void testWithDictionaryDynamicString(@From(AsciiStringGenerator.class) String input) {
//    }
//
//    public static void main(String[] args) throws IOException {
//        edu.berkeley.cs.jqf.examples.rhino.CompilerTest t = new edu.berkeley.cs.jqf.examples.rhino.CompilerTest();
//        t.initContext();
//        t.testWithString(new String(Files.readAllBytes(new File(args[0]).toPath())));
//    }


}
