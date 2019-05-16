package edu.berkeley.cs.jqf.examples.tomcat;



public class OGNLInjection  {
    private static Boolean injectionDetected = false;

    public OGNLInjection() {
    }

    public static void setInjectionDetected(Boolean val) {
        System.out.println("WE DID IT!!!");
        injectionDetected = val;
    }

    public static Boolean getInjectionDetected() {
        return injectionDetected;
    }
}
