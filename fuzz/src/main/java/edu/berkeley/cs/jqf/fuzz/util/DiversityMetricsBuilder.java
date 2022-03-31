package edu.berkeley.cs.jqf.fuzz.util;

import org.eclipse.collections.api.iterator.IntIterator;
import org.eclipse.collections.api.list.primitive.IntList;

/**
 * Based on the original code by Hoang Lam Nguyen, licensed under BSD-2-Clause license: https://github.com/hub-se/BeDivFuzz
 * https://github.com/hub-se/BeDivFuzz/blob/main/fuzz/src/main/java/de/hub/se/jqf/fuzz/div/DivMetricsCounter.java
 *
 */
public class DiversityMetricsBuilder {
    public static class HillNumbers{
        public double h_0;
        public double h_1;
        public double h_2;
    }
    public static HillNumbers hillNumbersFromCoverage(Coverage coverageAccumulatedFromUniqueTraces) {
        ReliableCounter counter = coverageAccumulatedFromUniqueTraces.getCounter();
        HillNumbers ret = new HillNumbers();
        IntList coveredBranchCounts = counter.getNonZeroValues();
        double shannon = 0;
        double h_0 = 0;
        double h_2 = 0;
        double totalBranchHitCount = coveredBranchCounts.sum();

        IntIterator iter = coveredBranchCounts.intIterator();
        while(iter.hasNext()){
            int hit_count = iter.next();

            double  p_i = ((double) hit_count) / totalBranchHitCount;
            shannon += p_i * Math.log(p_i);

            h_0 += Math.pow(p_i, 0);
            h_2 += Math.pow(p_i, 2);

        }
        ret.h_0 = Math.pow(h_0, 1); // Hill-Number of order 0
        ret.h_1 = Math.exp(-shannon); // Hill-number of order 1 (= exp(shannon_index))
        ret.h_2 = Math.pow(h_2, 1/(1-2)); // Hill-number of order 2
        return ret;
    }
}
