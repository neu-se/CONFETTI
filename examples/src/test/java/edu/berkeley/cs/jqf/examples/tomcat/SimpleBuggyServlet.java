package edu.berkeley.cs.jqf.examples.tomcat;


import java.io.*;
import java.util.Enumeration;
import javax.servlet.*;
import javax.servlet.http.*;


public class SimpleBuggyServlet extends HttpServlet {

    public void doGet(HttpServletRequest request, HttpServletResponse response)
            throws IOException {

        // System.out.println("IN SERVLET!");

        for (Enumeration<String> headerNames = request.getHeaderNames(); headerNames.hasMoreElements(); ) {
            String name = headerNames.nextElement();
        //    System.out.println(name);
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
      //  System.out.println("IN DO IF");
        if (n == 2) {
       //     System.out.println("CRASHING!");
            throw new IllegalStateException("Crash!");
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
}

