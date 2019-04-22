package edu.berkeley.cs.jqf.examples.tomcat;

import com.pholser.junit.quickcheck.From;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.examples.http.HTTPRequestGenerator;
import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.apache.coyote.ProtocolHandler;
import org.apache.coyote.http11.AbstractHttp11Protocol;
import org.apache.coyote.http11.Http11NioProtocol;
import org.apache.coyote.http11.Http11Processor;
import org.apache.http.Header;
import org.apache.http.client.methods.HttpUriRequest;
import org.apache.tomcat.util.net.*;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Rule;
import org.junit.rules.ExternalResource;
import org.junit.runner.RunWith;
import org.junit.runners.model.Statement;


import java.io.*;
import java.net.UnknownHostException;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.List;


@RunWith(JQF.class)
public class HTTPRequestTest extends TomcatBaseTest {

    private boolean accessLogEnabled = false;

    private static File tempDir;

    private final String webapp_string = "struts2-showcase-2_3_20_1";

    private static boolean tomcatTeardown = false;

    private List<File> deleteOnTearDown = new ArrayList<>();

    public static final String FAIL_50X = "HTTP/1.1 50";

    public File getTemporaryDirectory() {
        return tempDir;
    }


    @Rule
    public final ExternalResource myWebApp = new ExternalResource() {
        @Override
        protected void before() throws Throwable {
            System.out.println("SECOND BEFORE!");
            addWebApp(webapp_string);
        }
    };

    protected String getProtocol() {
        // Has a protocol been specified
        String protocol = System.getProperty("tomcat.test.protocol");

        // Use NIO by default starting with Tomcat 8
        if (protocol == null) {
            protocol = Http11NioProtocol.class.getName();
        }

        return protocol;
    }


    public void addDeleteOnTearDown(File file) {
        deleteOnTearDown.add(file);
    }
//
//    public static File getBuildDirectory() {
//        return new File(System.getProperty("tomcat.test.tomcatbuild",
//                "output/build"));
//    }


//    @After
//    public void tearDown() throws Exception {
//        // Some tests may call tomcat.destroy(), some tests may just call
//        // tomcat.stop(), some not call either method. Make sure that stop()
//        // & destroy() are called as necessary.
//
//        if (HTTPRequestTest.tomcatTeardown) {
//            if (tomcat.getServer() != null
//                    && tomcat.getServer().getState() != LifecycleState.DESTROYED) {
//                if (tomcat.getServer().getState() != LifecycleState.STOPPED) {
//                    tomcat.stop();
//                }
//                tomcat.destroy();
//            }
//
//            tomcat = null;
//        }
//    }

//    @Fuzz
//    public void parseHTTPRequest(byte[] input) {
//        Assume.assumeTrue(input.length < 200);
//        HeaderParser parser = new HeaderParser(input);
//        try {
//            parser.parseHeaders();
//        } catch (IllegalArgumentException e) {
//            Assume.assumeNoException(e);
//        } catch (IOException e) {
//            throw new RuntimeException(e);
//        }
//    }

//
//    protected void addSimpleBuggyWebappToTomcat(boolean addJstl, boolean start)
//            throws ServletException, LifecycleException {
//
//        Context ctx = tomcat.addContext("", null);
//        Tomcat.addServlet(ctx, "simplebuggy", new SimpleBuggyServlet());
//        ctx.addServletMappingDecoded("/", "simplebuggy");
//
//
//        if (start) {
//            tomcat.start();
//        }
//    }


    @Fuzz
    public void processHTTPRequest(String input) {

        try {
            String request = input;
//            request = "GET /struts2-showcase-2_3_20_1/index.action HTTP/1.1\r\n" +
//                    "Host: any\r\n" +
//                    "User-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:66.0) Gecko/20100101 Firefox/66.0\r\n" +
//                    "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n" +
//                    "Accept-Language: en-US,en;q=0.5\r\n" +
//                    "Accept-Encoding: gzip, deflate\r\n" +
//                    "Connection: keep-alive\r\n" +
//                    "Cookie: JSESSIONID=B8071E5AAEDED6181D7C0ACFFBA3D862\r\n" +
//                    "Upgrade-Insecure-Requests: 1\r\n" +
//                    "Cache-Control: max-age=0\r\n\r\n";
            request = "POST /" + webapp_string + "/integration/saveGangster.action HTTP/1.1\r\n" +
                    "Host: any\r\n" +
                    "User-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:66.0) Gecko/20100101 Firefox/66.0\r\n" +
                    "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n" +
                    "Accept-Language: en-US,en;q=0.5\r\n" +
                    "Accept-Encoding: gzip, deflate\r\n" +
                    "Referer: http://localhost:8080/struts2-showcase-2_3_10/integration/editGangster\r\n" +
                    "Content-Type: application/x-www-form-urlencoded\r\n" +
                    "Content-Length: 708\r\n" +
                    "Connection: keep-alive\r\n" +
                    "Cookie: JSESSIONID=355085EC5421F19AF97B123A53841DF7\r\n" +
                    "Upgrade-Insecure-Requests: 1\r\n\r\n" +
                    "name=%25%7B%28%23dm%3D%40ognl.OgnlContext%40DEFAULT_MEMBER_ACCESS%29.%28%23_memberAccess%3F%28%23_memberAccess%3D%23dm%29%3A%28%28%23container%3D%23context%5B%27com.opensymphony.xwork2.ActionContext.container%27%5D%29.%28%23ognlUtil%3D%23container.getInstance%28%40com.opensymphony.xwork2.ognl.OgnlUtil%40class%29%29.%28%23ognlUtil.getExcludedPackageNames%28%29.clear%28%29%29.%28%23ognlUtil.getExcludedClasses%28%29.clear%28%29%29.%28%23context.setMemberAccess%28%23dm%29%29%29%29.%28%40edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection%40setInjectionDetected%28true%29%29.%28%40java.lang.Runtime%40getRuntime%28%29.exec%28%27ls%27%29%29%7D&age=33&bustedBefore=true&__checkbox_bustedBefore=true&description=\r\n\r\n";

            ProtocolHandler protocol = tomcat.getConnector().getProtocolHandler();
            AbstractHttp11Protocol<?> http11Protocol = (AbstractHttp11Protocol<?>) protocol;
            Http11Processor processor = new Http11Processor(http11Protocol, tomcat.getConnector().getProtocolHandler().getAdapter());
            ByteBuffer buf = ByteBuffer.wrap(request.getBytes());

            SocketWrapper wrapper = new SocketWrapper(buf);
            processor.service(wrapper);

            BufferedReader reader = new BufferedReader(new InputStreamReader(new ByteArrayInputStream(wrapper.getOut().array())));

            String line = reader.readLine();

            System.out.println(line);
            if (line.startsWith("\0")) {
                throw new IllegalStateException("SERVER EXCEPTION!");
            }
            else if (OGNLInjection.getInjectionDetected()) {
                System.out.println("HELLO THERE!");
                OGNLInjection.setInjectionDetected(false);
                throw new IllegalStateException("OGNL Injection Detected!");
            }
        } catch (UnknownHostException e) {
            Assume.assumeNoException(e);
        } catch (IOException e) {
            Assume.assumeNoException(e);
        }


    }

    @Fuzz
    public void parseHTTPRequestHeadersWithGenerator(@From(HTTPRequestGenerator.class) @Dictionary("dictionaries/tomcat-http-request.dict") HttpUriRequest req) {
        String request = req.toString() + "\r\n";

        Header[] headerFields = req.getAllHeaders();
        for (int i = 0; i < headerFields.length; i++) {
            request += (headerFields[i].getName() + ": " + headerFields[i].getValue() + "\r\n");
        }
        request += "\r\n";


        try {

            request = "POST /" + webapp_string + "/integration/saveGangster.action HTTP/1.1\r\n" +
                    "Host: any\r\n" +
                    "User-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:66.0) Gecko/20100101 Firefox/66.0\r\n" +
                    "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n" +
                    "Accept-Language: en-US,en;q=0.5\r\n" +
                    "Accept-Encoding: gzip, deflate\r\n" +
                    "Referer: http://localhost:8080/struts2-showcase-2_3_10/integration/editGangster\r\n" +
                    "Content-Type: application/x-www-form-urlencoded\r\n" +
                    "Content-Length: 708\r\n" +
                    "Connection: keep-alive\r\n" +
                    "Cookie: JSESSIONID=355085EC5421F19AF97B123A53841DF7\r\n" +
                    "Upgrade-Insecure-Requests: 1\r\n\r\n" +
                    "name=%25%7B%28%23dm%3D%40ognl.OgnlContext%40DEFAULT_MEMBER_ACCESS%29.%28%23_memberAccess%3F%28%23_memberAccess%3D%23dm%29%3A%28%28%23container%3D%23context%5B%27com.opensymphony.xwork2.ActionContext.container%27%5D%29.%28%23ognlUtil%3D%23container.getInstance%28%40com.opensymphony.xwork2.ognl.OgnlUtil%40class%29%29.%28%23ognlUtil.getExcludedPackageNames%28%29.clear%28%29%29.%28%23ognlUtil.getExcludedClasses%28%29.clear%28%29%29.%28%23context.setMemberAccess%28%23dm%29%29%29%29.%28%40edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection%40setInjectionDetected%28true%29%29.%28%40java.lang.Runtime%40getRuntime%28%29.exec%28%27ls%27%29%29%7D&age=33&bustedBefore=true&__checkbox_bustedBefore=true&description=\r\n\r\n";

            ProtocolHandler protocol = tomcat.getConnector().getProtocolHandler();
            AbstractHttp11Protocol<?> http11Protocol = (AbstractHttp11Protocol<?>) protocol;
            Http11Processor processor = new Http11Processor(http11Protocol, tomcat.getConnector().getProtocolHandler().getAdapter());

            // System.out.println(request);
            ByteBuffer buf = ByteBuffer.wrap(request.getBytes());

            SocketWrapper wrapper = new SocketWrapper(buf);
            processor.service(wrapper);

            BufferedReader reader = new BufferedReader(new InputStreamReader(new ByteArrayInputStream(wrapper.getOut().array())));

            String line = reader.readLine();
            //System.out.println(line);

            // For whatever reason, calling the HTTP11Processor yields an empty response in the case of an Exception
            // on the server end.
            if (line.startsWith("\0")) {
                throw new IllegalStateException("SERVER EXCEPTION!");
            }
            else if (OGNLInjection.getInjectionDetected()) {
                OGNLInjection.setInjectionDetected(false);
                throw new OGNLInjectionException("OGNL Injection Detected!");
            }


        } catch (UnknownHostException e) {
            Assume.assumeNoException(e);
        } catch (IOException e) {
            Assume.assumeNoException(e);
        }


    }

    private static class SocketWrapper extends SocketWrapperBase<Void> {

        final ByteBuffer in;
        ByteBuffer out;

        SocketWrapper(ByteBuffer in) {
            super(null, null);
            this.in = in;
            this.out = ByteBuffer.wrap(new byte[1024*1024]);
            this.socketBufferHandler = new SocketBufferHandler(4096, 4096, true);
        }

        public ByteBuffer getOut() {
            return this.out;
        }

        @Override
        protected void populateRemoteHost() {

        }

        @Override
        protected void populateRemoteAddr() {

        }

        @Override
        protected void populateRemotePort() {

        }

        @Override
        protected void populateLocalName() {

        }

        @Override
        protected void populateLocalAddr() {

        }

        @Override
        protected void populateLocalPort() {

        }

        @Override
        public int read(boolean block, byte[] b, int off, int len) throws IOException {
            throw new UnsupportedOperationException();
        }

        @Override
        public int read(boolean block, ByteBuffer to) throws IOException {
            int start = in.position();
            to.put(in);
            int end = in.position();
            return end - start;
        }

        @Override
        public boolean isReadyForRead() throws IOException {
            return in.position() < in.limit();
        }

        @Override
        public void setAppReadBufHandler(ApplicationBufferHandler handler) {

        }

        @Override
        public void close() throws IOException {

        }

        @Override
        public boolean isClosed() {
            return false;
        }

        @Override
        protected void doWrite(boolean block, ByteBuffer from) throws IOException {
            this.out.put(from);
            return;
        }

        @Override
        public void registerReadInterest() {

        }

        @Override
        public void registerWriteInterest() {

        }

        @Override
        public SendfileDataBase createSendfileData(String filename, long pos, long length) {
            throw new UnsupportedOperationException();
        }

        @Override
        public SendfileState processSendfile(SendfileDataBase sendfileData) {
            throw new UnsupportedOperationException();
        }

        @Override
        public void doClientAuth(SSLSupport sslSupport) throws IOException {
            throw new UnsupportedOperationException();
        }

        @Override
        public SSLSupport getSslSupport(String clientCertProvider) {
            throw new UnsupportedOperationException();
        }
    }


    public static void main(String[] args) throws Throwable {

        HTTPRequestTest test = new HTTPRequestTest();
        test.resource.apply(new Statement() {
            @Override
            public void evaluate() throws Throwable {

            }
        }, null).evaluate();
        test.myWebApp.apply(new Statement() {
            @Override
            public void evaluate() throws Throwable {

            }
        }, null).evaluate();
     //  HTTPRequestTest.tomcat.getServer().await();



//       String request = "GET /struts2-showcase-2_3_20_1/index.action HTTP/1.1\r\n" +
//               "Host: any\r\n" +
//               "User-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:66.0) Gecko/20100101 Firefox/66.0\r\n" +
//               "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n" +
//               "Accept-Language: en-US,en;q=0.5\r\n" +
//               "Accept-Encoding: gzip, deflate\r\n" +
//               "Connection: keep-alive\r\n" +
//               "Cookie: JSESSIONID=B8071E5AAEDED6181D7C0ACFFBA3D862\r\n" +
//               "Upgrade-Insecure-Requests: 1\r\n" +
//               "Cache-Control: max-age=0\r\n\r\n";
        String request = "POST /" + test.webapp_string + "/integration/saveGangster.action HTTP/1.1\r\n" +
                "Host: any\r\n" +
                "User-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:66.0) Gecko/20100101 Firefox/66.0\r\n" +
                "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n" +
                "Accept-Language: en-US,en;q=0.5\r\n" +
                "Accept-Encoding: gzip, deflate\r\n" +
                "Referer: http://localhost:8080/struts2-showcase-2_3_10/integration/editGangster\r\n" +
                "Content-Type: application/x-www-form-urlencoded\r\n" +
                "Content-Length: 708\r\n" +
                "Connection: keep-alive\r\n" +
                "Cookie: JSESSIONID=355085EC5421F19AF97B123A53841DF7\r\n" +
                "Upgrade-Insecure-Requests: 1\r\n\r\n" +
                "name=%25%7B%28%23dm%3D%40ognl.OgnlContext%40DEFAULT_MEMBER_ACCESS%29.%28%23_memberAccess%3F%28%23_memberAccess%3D%23dm%29%3A%28%28%23container%3D%23context%5B%27com.opensymphony.xwork2.ActionContext.container%27%5D%29.%28%23ognlUtil%3D%23container.getInstance%28%40com.opensymphony.xwork2.ognl.OgnlUtil%40class%29%29.%28%23ognlUtil.getExcludedPackageNames%28%29.clear%28%29%29.%28%23ognlUtil.getExcludedClasses%28%29.clear%28%29%29.%28%23context.setMemberAccess%28%23dm%29%29%29%29.%28%40edu.berkeley.cs.jqf.examples.tomcat.OGNLInjection%40setInjectionDetected%28true%29%29.%28%40java.lang.Runtime%40getRuntime%28%29.exec%28%27ls%27%29%29%7D&age=33&bustedBefore=true&__checkbox_bustedBefore=true&description=\r\n\r\n";

        test.processHTTPRequest(request);
    }
}