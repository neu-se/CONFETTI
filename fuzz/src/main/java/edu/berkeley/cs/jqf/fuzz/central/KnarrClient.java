package edu.berkeley.cs.jqf.fuzz.central;

import edu.berkeley.cs.jqf.fuzz.guidance.StringEqualsHintingInputStream;
import sun.awt.image.ImageWatched;
import za.ac.sun.cs.green.expr.Expression;

import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

public class KnarrClient extends Central {

    public KnarrClient() throws IOException {
        super();
        oos.writeObject(Type.Knarr);
        oos.flush();
    }
    public byte[] getInput() throws IOException {
        try {


            byte[] ret = (byte[]) ois.readObject();
            LinkedList<String[]> hints = (LinkedList<String[]>) ois.readObject();
            if(!hints.isEmpty()) {
                //System.out.println("IN KNARR PROCESS - GOT INPUT WITH HINTS!!!");
                StringEqualsHintingInputStream is = new StringEqualsHintingInputStream(hints);
            }
            return ret;
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    public void sendConstraints(LinkedList<Expression> constraints) throws IOException {
        oos.writeObject(constraints);
        oos.reset();
        oos.flush();
    }
}
