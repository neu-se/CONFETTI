package edu.berkeley.cs.jqf.examples.tomcat;

import com.pholser.junit.quickcheck.From;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.examples.http.HTTPRequestGenerator;
import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.apache.coyote.http11.HeaderParser;
import org.apache.http.client.methods.HttpUriRequest;
import org.junit.Assume;
import org.junit.runner.RunWith;

import java.io.IOException;


@RunWith(JQF.class)
public class HTTPRequestTest {

    @Fuzz
    public void parseHTTPRequest(byte[] input) {
        Assume.assumeTrue(input.length < 200);
        HeaderParser parser = new HeaderParser(input);
        try {
            parser.parseHeaders();
        } catch (IllegalArgumentException e) {
            Assume.assumeNoException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Fuzz
    public void parseHTTPRequestWithGenerator(@From(HTTPRequestGenerator.class) HttpUriRequest req) {
        try {
            parseHTTPRequest(req.toString().getBytes());
        } catch (IllegalArgumentException e) {
            Assume.assumeNoException(e);
        }
    }
}