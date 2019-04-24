package edu.berkeley.cs.jqf.fuzz.knarr;

import edu.berkeley.cs.jqf.fuzz.junit.GuidedFuzzing;

public class KnarrDriver {

    public static void main(String[] args) {
        if (args.length < 2){
            System.err.println("Usage: java " + KnarrDriver.class + " TEST_CLASS TEST_METHOD");
            System.exit(1);
        }

        String testClassName  = args[0];
        String testMethodName = args[1];

        try {
            // Load the guidance
            String title = testClassName+"#"+testMethodName;
            KnarrGuidance guidance = new KnarrGuidance();

            // Run the Junit test
            GuidedFuzzing.run(testClassName, testMethodName, guidance, System.out);

        } catch (Exception e) {
            e.printStackTrace();
            System.exit(2);
        }

    }
}
