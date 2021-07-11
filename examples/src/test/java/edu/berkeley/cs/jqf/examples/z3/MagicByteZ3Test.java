package edu.berkeley.cs.jqf.examples.z3;

import com.pholser.junit.quickcheck.From;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.junit.runner.RunWith;

@RunWith(JQF.class)

public class MagicByteZ3Test {
    @Fuzz
    public void testStringOnly(@From(MagicByteBranches.MagicInputGenerator.class)
                                  @Dictionary("dictionaries/maven-model.dict")
                                              MagicByteBranches.MagicInput input) {
        MagicByteBranches.examineInputStringOnly(input);
    }
    @Fuzz
    public void testIntsOnly(@From(MagicByteBranches.MagicInputGenerator.class)
                               @Dictionary("dictionaries/maven-model.dict")
                                       MagicByteBranches.MagicInput input) {
        MagicByteBranches.examineInputIntsOnly(input);
    }
}
