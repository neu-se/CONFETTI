import com.pholser.junit.quickcheck.From;
import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.junit.runner.RunWith;

@RunWith(JQF.class)
public class HardTest {

    @Fuzz
    public void testHardToFind(@From(BytesGenerator.class) byte[] bs) {
        int i = 1;
        if(bs[0] == bs[BytesGenerator.SIZE / 2]) {
            i++;
        }
    }
}
