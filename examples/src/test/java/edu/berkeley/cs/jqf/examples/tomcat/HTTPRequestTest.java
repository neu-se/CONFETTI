package edu.berkeley.cs.jqf.examples.tomcat;

import com.pholser.junit.quickcheck.From;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.examples.http.HTTPRequestGenerator;
import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.apache.http.client.methods.HttpUriRequest;
import org.junit.Assume;
import org.junit.runner.RunWith;



@RunWith(JQF.class)
public class HTTPRequestTest {

    @Fuzz
    public void parseHTTPRequest(@From(HTTPRequestGenerator.class) HttpUriRequest req) {
        try {
            System.out.println(req.toString());
        } catch (IllegalArgumentException e) {
            Assume.assumeNoException(e);
        }
    }
}