package edu.berkeley.cs.jqf.examples.http;


import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;


import edu.berkeley.cs.jqf.examples.common.AlphaStringGenerator;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.examples.common.DictionaryBackedStringGenerator;
import org.apache.http.client.methods.RequestBuilder;
import org.apache.http.client.methods.HttpUriRequest;

import java.io.IOException;

public class HTTPRequestGenerator extends Generator<HttpUriRequest> {

    public HTTPRequestGenerator() {
        super(HttpUriRequest.class);
    }

    private final int max_elements = 5;

    @Override
    public HttpUriRequest generate(SourceOfRandomness random, GenerationStatus status) {
            RequestBuilder builder = getReqType(random, status);
            getHeaders(builder,random,status);
            getParameters(builder,random,status);
            return builder.build();
    }

    private Generator<String> stringGenerator = new AlphaStringGenerator();

    private Generator<String> randomStringGenerator = new AlphaStringGenerator();
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

    private String makeString(SourceOfRandomness random, GenerationStatus status) {
        return stringGenerator.generate(random, status);
    }

    private String makeAlphaString(SourceOfRandomness random, GenerationStatus status) {
        return randomStringGenerator.generate(random,status);
    }

    private RequestBuilder getReqType(SourceOfRandomness random, GenerationStatus status) {
        int index = random.nextInt(7);
        switch(index) {
            case 0:
                return RequestBuilder.get(makeString(random, status));
            case 1:
                return RequestBuilder.post(makeString(random, status));
            case 2:
                return RequestBuilder.patch(makeString(random, status));
            case 3:
                return RequestBuilder.head(makeString(random, status));
            case 4:
                return RequestBuilder.delete(makeString(random, status));
            case 5:
                return RequestBuilder.trace(makeString(random, status));
            case 6:
                return RequestBuilder.delete(makeString(random, status));

             // shouldn't get here
            default:
                return null;
        }

    }

    private void getHeaders(RequestBuilder builder, SourceOfRandomness random, GenerationStatus status) {
        int index = random.nextInt(max_elements);
        for(int i = 0; i< index; i++) {
            builder.addHeader(makeAlphaString(random, status), makeAlphaString(random,status));
        }
    }
    private void getParameters(RequestBuilder builder, SourceOfRandomness random, GenerationStatus status) {
        int index = random.nextInt(max_elements);
        for(int i = 0; i< index; i++) {
            builder.addParameter(makeAlphaString(random, status), makeAlphaString(random,status));
        }
    }
}
