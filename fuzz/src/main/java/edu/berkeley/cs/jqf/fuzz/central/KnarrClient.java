package edu.berkeley.cs.jqf.fuzz.central;

import java.io.IOException;

public class KnarrClient extends Central {

    public KnarrClient() throws IOException {
        super();
        oos.writeObject(Type.Knarr);
        oos.flush();
    }

    public byte[] getInput() throws IOException {
        try {
            return (byte[]) ois.readObject();
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }
}
