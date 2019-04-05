package edu.berkeley.cs.jqf.fuzz.ei;

import edu.berkeley.cs.jqf.fuzz.guidance.Result;
import edu.berkeley.cs.jqf.fuzz.util.Coverage;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.LinkedList;

public class Central {
    private Socket s;
    private ObjectInputStream ois;
    private ObjectOutputStream oos;

    public static Central connect() {
        try {
            Socket s = new Socket(InetAddress.getLocalHost(), 54321);
            Central c = new Central();
            c.ois = new ObjectInputStream(s.getInputStream());
            c.oos = new ObjectOutputStream(s.getOutputStream());

            return c;
        } catch (IOException e) {
            return null;
        }
    }

    /* Client:
     * 1. Send input
     * 2. Send coverage
     * 3. Select input
     * 3. Receive instructions
     */

    public void sendInput(LinkedList<byte[]> inputRequests, Result result, int id) throws IOException {
        oos.writeObject(inputRequests);
        oos.writeObject(result);
        oos.writeInt(id);
        oos.flush();
    }

    public void sendCoverage(Coverage cov) throws IOException {
        // TODO
    }

    public void selectInput(int id) throws IOException {
        oos.writeObject(new Integer(id));
    }

    private void receiveResult() {
        throw new Error("Not implemented");
    }

    public LinkedList<int[]> receiveInstructions() throws IOException {
        try {

            return (LinkedList<int[]>) ois.readObject();
        } catch (ClassNotFoundException e) {
            throw new Error(e);
        }
    }

    /* Server:
     * 1. Receive input
     * 2. Receive coverage
     * 3. Receive selected input
     * 3. Send instructions
     */
    public static void main(String[] args) throws Throwable {
        ServerSocket ss = new ServerSocket(54321);

        Socket s = ss.accept();

        ObjectOutputStream oos = new ObjectOutputStream(s.getOutputStream());
        ObjectInputStream ois = new ObjectInputStream(s.getInputStream());

        ArrayList<LinkedList<byte[]>> inputs = new ArrayList<>();
        ArrayList<Integer> fuzzing = new ArrayList<>();

        while (true) {
            // Receive input or select new input
            Object o = ois.readObject();

            if (o instanceof LinkedList) {
                // Receive input
                LinkedList<byte[]> inputRequests = (LinkedList<byte[]>) o;
                Result res = (Result) ois.readObject();
                int id = ois.readInt();

                // Receive coverage
//                Coverage cov = (Coverage) ois.readObject();

                // Save input
                inputs.add(id, inputRequests);
                fuzzing.add(id, 0);

            } else if (o instanceof Integer) {
                // Select input
                int selected = (Integer)o;

                // Select part of the input to fuzz
                int i = 0;
                int offset = 0;
                int size = 0;
                int toFuzz = fuzzing.get(selected);
                LinkedList<int[]> instructionsToSend = new LinkedList<>();
                for (byte[] b : inputs.get(selected)) {
                    instructionsToSend.addLast(new int[]{offset, b.length});
                    offset += b.length;
                }

                // Send instructions
                oos.writeObject(instructionsToSend);

                // Update state
                fuzzing.set(selected, (toFuzz + 1) % inputs.get(selected).size());
            }
        }
    }
}
