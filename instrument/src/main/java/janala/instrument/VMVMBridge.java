package janala.instrument;

//import edu.columbia.cs.psl.vmvm.runtime.ConsumerUtils;

public class VMVMBridge {//extends ConsumerUtils {
	//@Override
	public boolean isIgnoredClass(String internalName) {
		if (internalName.startsWith("edu/berkeley/cs/jqf/instrument")
				|| internalName.startsWith("edu/berkeley/cs/jqf/fuzz") ||
				internalName.startsWith("janala/"))
			return true;
		return false;
	}
}
