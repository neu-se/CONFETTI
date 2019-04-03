package edu.berkeley.cs.jqf.examples.tomcat;


import java.io.*;
import java.util.Enumeration;
import javax.servlet.*;
import javax.servlet.http.*;


public class SimpleBuggyServlet extends HttpServlet {

    public void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        System.out.println("IN DO GET!!");
        for (Enumeration<String> headerNames = request.getHeaderNames(); headerNames.hasMoreElements(); ) {
            String name = headerNames.nextElement();
            System.out.println(name);
            for(int i = 0; i < name.length(); i++) {

                char x = name.charAt(i);
                doIf((x - '0') % 10);
                doFor((x-'0') % 10);
                doLookupSwitch((x-'0') % 10);
                doTableSwitch((x-'0') % 10);
            }
            
        }

        String message = "TESTING!!";
        // Set response content type
        response.setContentType("text/html");
        // Set status of response
        response.setStatus(200);

        // Actual logic goes here.
        PrintWriter out = response.getWriter();
        out.println("<h1>" + message + "</h1>");
    }

    public void destroy() {
        // do nothing.
    }


    // 2 paths
    public void doIf(int n) {
        if (n == 2) {
            throw new RuntimeException("Crash!");
        }
    }

    // since n <= 9, 10 paths
    public void doFor(int n) {
        for (int i = 0; i < n; i++) {
            int y = 0;
        }
    }

    // 3 paths
    public int doLookupSwitch(int n) {
        int z;

        // lookup switch
        switch(n) {
            case 2:  z = 4; break;
            case 4: z = 7; break;
            default: z = -1;
        }

        return z;
    }

    // 4 paths
    public int doTableSwitch(int n) {
        int z;

        // table switch
        switch(n) {
            case 1: z = 1; break;
            case 2: z = 2; break;
            case 3: z = 3; break;
            default: z = -1;
        }

        return z;
    }

//    /**
//     * Parses 4 characters from a file as integers and calls the above methods.
//     **/
//    public static void main(String args[]) {
//        byte[] password = new byte[8];
//        int bytes_read = 0;
//
//        // if(!SimpleBuggy.gatekeeper){
//
//        SimpleBuggy x = new SimpleBuggy();
//        try (FileInputStream stream = new FileInputStream(args[0])) {
//
//            bytes_read = stream.read(password);
//            String p_string = new String(password);
//            // if(!p_string.equals("password")) {
//            // 	SimpleBuggy.gatekeeper = true;
//            // 	throw new RuntimeException("INCORRECT MAGIC!");
//            // }
//
//            x.doIf((stream.read()-'0') % 10);
//            x.doFor((stream.read()-'0') % 10);
//            x.doLookupSwitch((stream.read()-'0') % 10);
//            x.doTableSwitch((stream.read()-'0') % 10);
//
//        } catch (FileNotFoundException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//        } catch (IOException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//        }
//        // }
//        // else {
//        // // 	throw new RuntimeException("You cannot proceed without the right magic!!");
//        // }
//        System.out.println("Main done.");
//    }
}

