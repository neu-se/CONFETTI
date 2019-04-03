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

    private String makeMultiLineString(SourceOfRandomness random, GenerationStatus status) {
        String final_string = randomStringGenerator.generate(random,status);
        while(random.nextBoolean()) {
            final_string += "\n";
            final_string += randomStringGenerator.generate(random, status);
        }
        return final_string;
    }

    private RequestBuilder getReqType(SourceOfRandomness random, GenerationStatus status) {
        int index = random.nextInt(1);
        switch(index) {
            case 0:
                return RequestBuilder.get("/");
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

    private void getHeaders(RequestBuilder builder, SourceOfRandomness random, GenerationStatus status) {
        int index = random.nextInt(max_elements);
        boolean useDict  = random.nextBoolean();

        for(int i = 0; i< index; i++) {
//            if (useDict)
                builder.addHeader(makeString(random, status), makeMultiLineString(random,status));
//            else
//                builder.addHeader(makeAlphaString(random, status), makeAlphaString(random,status));
        }
    }
    private void getParameters(RequestBuilder builder, SourceOfRandomness random, GenerationStatus status) {
        int index = random.nextInt(max_elements);
        for(int i = 0; i< index; i++) {
            builder.addParameter(makeAlphaString(random, status), makeAlphaString(random,status));
        }
    }
}
