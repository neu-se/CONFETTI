/*
 * Copyright (c) 2017-2018 The Regents of the University of California
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package edu.berkeley.cs.jqf.fuzz.extendedDictionary;

import edu.berkeley.cs.jqf.fuzz.junit.GuidedFuzzing;
import edu.berkeley.cs.jqf.fuzz.knarr.KnarrGuidance;
import edu.columbia.cs.psl.phosphor.PreMain;

import java.io.File;
import java.util.ArrayList;

public class ExtendedDictionaryEvaluatorDriver {

    public static void main(String[] args) {
        if (args.length < 3){
            System.err.println("Usage: java " + ExtendedDictionaryEvaluatorDriver.class + " TEST_CLASS TEST_METHOD TEST_INPUT_FILE...");
            System.exit(1);
        }


        String testClassName  = args[0];
        String testMethodName = args[1];
        File[] testInputFiles = null;
        ArrayList<File> validFiles = new ArrayList<>();
        for (int i = 0; i < args.length - 2; i++) {
            File inputArg = new File(args[i + 2]);
            if (inputArg.isDirectory()) {
                for (File f : inputArg.listFiles()) {
                    if (f.getName().endsWith(".input"))
                        continue;
                    validFiles.add(f);
                }
            } else {
                validFiles.add(inputArg);
            }
        }
        testInputFiles = new File[validFiles.size()];
        testInputFiles = validFiles.toArray(testInputFiles);
        try {
            // Maybe log the trace
            String outputFileName = System.getenv("EVAL_FILE");
            File outputFile = outputFileName != null ? new File(outputFileName) : null;

            // Load the guidance
            ExtendedDictionaryEvaluatorGuidance guidance = new ExtendedDictionaryEvaluatorGuidance(testInputFiles, outputFile);

            // Run the Junit test
            GuidedFuzzing.run(testClassName, testMethodName, guidance, (System.getenv("QUIET")  == null ? System.out : null));

            guidance.close();

            int nInputsWithExtendedDictHints = 0;
            int nInputsWithEQNonExtendedDictHints = 0;
            int nInputsWithEQNoNExtendedDictHintsButNotCounts = 0;
            for(ExtendedDictionaryEvaluatorGuidance.ExtendedDictionaryLinearInput input : guidance.analyzedInputs){
                if(!input.indicesOfHintsThatAreGlobalDictionaryHints.isEmpty()){
                    nInputsWithExtendedDictHints++;
                    if(input.numChildrenSameCovAndCounts > 0){
                        nInputsWithEQNonExtendedDictHints++;
                    } else if(input.numChildrenSameCovLessCounts > 0 ){
                        nInputsWithEQNoNExtendedDictHintsButNotCounts++;
                    }
                }
            }
            System.out.format("Examined %d inputs, %d with extended dict at %d trials per input. %d/%d could be replicated without the hints and get same counts, plus %d/%d that got same branches but not same hit counts.\n",
                    guidance.analyzedInputs.size(),
                    nInputsWithExtendedDictHints,
                    ExtendedDictionaryEvaluatorGuidance.NUM_TRIALS_PER_INPUT,
                    nInputsWithEQNonExtendedDictHints,
                    nInputsWithExtendedDictHints,
                    nInputsWithEQNoNExtendedDictHintsButNotCounts,
                    nInputsWithExtendedDictHints);
        } catch (Exception e) {
            e.printStackTrace();
            System.exit(2);
        }

    }
}
