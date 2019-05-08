package edu.berkeley.cs.jqf.examples.http;


import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;


import edu.berkeley.cs.jqf.examples.common.AlphaStringGenerator;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.examples.common.DictionaryBackedStringGenerator;
import org.apache.http.Header;
import org.apache.http.client.methods.RequestBuilder;
import org.apache.http.client.methods.HttpUriRequest;

import java.io.IOException;

public class HTTPRequestGenerator extends Generator<String> {

    public HTTPRequestGenerator() {
        super(String.class);
    }

    protected final int max_elements = 8;



    @Override
    public String generate(SourceOfRandomness random, GenerationStatus status) {
            RequestBuilder builder = getReqType(random, status);
            getHeaders(builder,random,status);

           // getParameters(builder,random,status);
            HttpUriRequest req =  builder.build();
            String request = req.toString() + "\r\n";

            Header[] headerFields = req.getAllHeaders();
            for (int i = 0; i < headerFields.length; i++) {
                request += (headerFields[i].getName() + ": " + headerFields[i].getValue() + "\r\n");
            }
            request += "\r\n";
            request += getBody();

        System.out.println(request);
            return request;
    }


    // Basic Http Request Generator returns request with no body
    protected String getBody() {
        return "";
    }

    protected Generator<String> stringGenerator = new AlphaStringGenerator();

    protected Generator<String> randomStringGenerator = new AlphaStringGenerator();
    /**
     * Configures the string generator used by this generator to use
     * a dictionary. This is useful for overriding the default
     * arbitrary string generator with something that pulls tag names
     * from a predefined list.
     *
     * @param dict the dictionary file
     * @throws IOException if the dictionary file cannot be read
     */
    public void configure(Dictionary dict) throws IOException {
        stringGenerator = new DictionaryBackedStringGenerator(dict.value(), stringGenerator);
    }

    protected String makeString(SourceOfRandomness random, GenerationStatus status) {
        return stringGenerator.generate(random, status);
    }

    protected String makeAlphaString(SourceOfRandomness random, GenerationStatus status) {
        return randomStringGenerator.generate(random,status);
    }

    protected String makeMultiLineString(SourceOfRandomness random, GenerationStatus status) {
        String final_string = randomStringGenerator.generate(random,status);
        while(random.nextBoolean()) {
            final_string += "\n";
            final_string += randomStringGenerator.generate(random, status);
        }
        return final_string;
    }

    protected RequestBuilder getReqType(SourceOfRandomness random, GenerationStatus status) {
        int index  = random.nextInt(5);
        switch(index) {
            case 0:
                return RequestBuilder.get(makeAlphaString(random, status));
            case 1:
                return RequestBuilder.post(makeAlphaString(random, status));
            case 2:
                return RequestBuilder.head(makeAlphaString(random, status));
            case 3:
                return RequestBuilder.delete(makeAlphaString(random, status));
            case 4:
                return RequestBuilder.trace(makeAlphaString(random, status));
             // shouldn't get here
            default:
                return null;
        }

    }

    protected void getHeaders(RequestBuilder builder, SourceOfRandomness random, GenerationStatus status) {
        int index = random.nextInt(max_elements);
        for(int i = 0; i< index; i++) {
                builder.addHeader(makeString(random, status), makeMultiLineString(random,status));

        }
    }
    protected void getParameters(RequestBuilder builder, SourceOfRandomness random, GenerationStatus status) {
        int index = random.nextInt(max_elements);
        for(int i = 0; i< index; i++) {
            builder.addParameter(makeAlphaString(random, status), makeAlphaString(random,status));
        }
    }
}
