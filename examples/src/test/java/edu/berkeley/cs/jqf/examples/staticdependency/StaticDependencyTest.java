package edu.berkeley.cs.jqf.examples.staticdependency;

import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.junit.runner.RunWith;

@RunWith(JQF.class)
public class StaticDependencyTest {
	static int depField;
	@Fuzz
	public void doStaticTest(int input){
		if(input < 10 && depField == 0) //Unique failures should be 2 if isolation is working
		{
			throw new IllegalStateException();
		}
		depField++;
	}
}
