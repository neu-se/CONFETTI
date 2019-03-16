import javax.imageio.ImageIO;
import javax.imageio.ImageReader;
import javax.imageio.stream.ImageInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;

import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.junit.Assume;
import org.junit.runner.RunWith;

@RunWith(JQF.class)
public class PngTest {

    @Fuzz /* JQF will generate inputs to this method */
    public void testRead(InputStream input)  {
        // Create parser
        ImageReader reader = ImageIO.getImageReadersByFormatName("png").next();

        // Decode image from input stream
        try {
            reader.setInput(ImageIO.createImageInputStream(input));

            // Bound dimensions to avoid OOM
            Assume.assumeTrue(reader.getHeight(0) <= 256);
            Assume.assumeTrue(reader.getWidth(0) <= 256);

            // Decode first image in the input stream
            reader.read(0); 
        } catch (IOException e) {
            // This exception signals invalid input and not a test failure
            Assume.assumeNoException(e);
        }
    }
}