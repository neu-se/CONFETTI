package edu.berkeley.cs.jqf.examples.tomcat;

import com.pholser.junit.quickcheck.From;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.examples.http.HTTPRequestGenerator;
import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.apache.catalina.*;
import org.apache.catalina.connector.Connector;
import org.apache.catalina.core.AprLifecycleListener;
import org.apache.catalina.core.StandardServer;
import org.apache.catalina.session.ManagerBase;
import org.apache.catalina.session.StandardManager;
import org.apache.catalina.startup.Tomcat;
import org.apache.catalina.valves.AccessLogValve;
import org.apache.catalina.webresources.StandardRoot;
import org.apache.coyote.ProtocolHandler;
import org.apache.coyote.Request;
import org.apache.coyote.http11.*;
import org.apache.http.Header;
import org.apache.http.client.methods.HttpUriRequest;
import org.apache.tomcat.util.net.*;
import org.apache.tomcat.util.scan.StandardJarScanFilter;
import org.apache.tomcat.util.scan.StandardJarScanner;
import org.junit.*;
import org.junit.runner.RunWith;

import java.io.File;
import java.io.IOException;
import java.net.InetAddress;
import java.nio.ByteBuffer;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;


@RunWith(JQF.class)
public class HTTPRequestTest {

    private Tomcat tomcat;

    private boolean accessLogEnabled = false;

    private static File tempDir;

    private List<File> deleteOnTearDown = new ArrayList<>();



    public File getTemporaryDirectory() {
        return tempDir;
    }


    @BeforeClass
    public static void setUpPerTestClass() throws Exception {
        // Create catalina.base directory
        File tempBase = new File(System.getProperty("tomcat.test.temp", "output/tmp"));
        if (!tempBase.mkdirs() && !tempBase.isDirectory()) {
            Assert.fail("Unable to create base temporary directory for tests");
        }
        Path tempBasePath = FileSystems.getDefault().getPath(tempBase.getAbsolutePath());
        tempDir = Files.createTempDirectory(tempBasePath, "test").toFile();

        System.setProperty("catalina.base", tempDir.getAbsolutePath());

        // Configure logging
        System.setProperty("java.util.logging.manager",
                "org.apache.juli.ClassLoaderLogManager");
        System.setProperty("java.util.logging.config.file",
                new File(System.getProperty("tomcat.test.basedir"),
                        "conf/logging.properties").toString());

    }


    @Before
    public void setUp() throws Exception {


        File appBase = new File(getTemporaryDirectory(), "webapps");
        if (!appBase.exists() && !appBase.mkdir()) {
            Assert.fail("Unable to create appBase for test");
        }

        tomcat = new TomcatWithFastSessionIDs();

        String protocol = getProtocol();
        Connector connector = new Connector(protocol);
        // Listen only on localhost
        connector.setAttribute("address",
                InetAddress.getByName("localhost").getHostAddress());
        // Use random free port
        connector.setPort(0);
        // Mainly set to reduce timeouts during async tests
        connector.setAttribute("connectionTimeout", "3000");
        tomcat.getService().addConnector(connector);
        tomcat.setConnector(connector);

        // Add AprLifecycleListener if we are using the Apr connector
        if (protocol.contains("Apr")) {
            StandardServer server = (StandardServer) tomcat.getServer();
            AprLifecycleListener listener = new AprLifecycleListener();
            listener.setSSLRandomSeed("/dev/urandom");
            server.addLifecycleListener(listener);
            connector.setAttribute("pollerThreadCount", Integer.valueOf(1));
        }

        File catalinaBase = getTemporaryDirectory();
        tomcat.setBaseDir(catalinaBase.getAbsolutePath());
        tomcat.getHost().setAppBase(appBase.getAbsolutePath());

        accessLogEnabled = Boolean.parseBoolean(
                System.getProperty("tomcat.test.accesslog", "false"));
        if (accessLogEnabled) {
            String accessLogDirectory = System
                    .getProperty("tomcat.test.reports");
            if (accessLogDirectory == null) {
                accessLogDirectory = new File(getBuildDirectory(), "logs")
                        .toString();
            }
            AccessLogValve alv = new AccessLogValve();
            alv.setDirectory(accessLogDirectory);
            alv.setPattern("%h %l %u %t \"%r\" %s %b %I %D");
            tomcat.getHost().getPipeline().addValve(alv);
        }

        // Cannot delete the whole tempDir, because logs are there,
        // but delete known subdirectories of it.
        addDeleteOnTearDown(new File(catalinaBase, "webapps"));
        addDeleteOnTearDown(new File(catalinaBase, "work"));
    }

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

    public static File getBuildDirectory() {
        return new File(System.getProperty("tomcat.test.tomcatbuild",
                "output/build"));
    }


    @After
    public void tearDown() throws Exception {
            // Some tests may call tomcat.destroy(), some tests may just call
            // tomcat.stop(), some not call either method. Make sure that stop()
            // & destroy() are called as necessary.
            if (tomcat.getServer() != null
                    && tomcat.getServer().getState() != LifecycleState.DESTROYED) {
                if (tomcat.getServer().getState() != LifecycleState.STOPPED) {
                    tomcat.stop();
                }
                tomcat.destroy();
            }
    }

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


    public Tomcat getTomcatInstanceTestWebapp(boolean addJstl, boolean start)
            throws LifecycleException {
        File appDir = new File("test/webapp");
        Context ctx = tomcat.addWebapp(null, "/test", appDir.getAbsolutePath());

        StandardJarScanner scanner = (StandardJarScanner) ctx.getJarScanner();
        StandardJarScanFilter filter = (StandardJarScanFilter) scanner.getJarScanFilter();
        filter.setTldSkip(filter.getTldSkip() + ",testclasses");
        filter.setPluggabilitySkip(filter.getPluggabilitySkip() + ",testclasses");

        if (addJstl) {
            File lib = new File("webapps/examples/WEB-INF/lib");
            ctx.setResources(new StandardRoot(ctx));
            ctx.getResources().createWebResourceSet(
                    WebResourceRoot.ResourceSetType.POST, "/WEB-INF/lib",
                    lib.getAbsolutePath(), null, "/");
        }

        if (start) {
            tomcat.start();
        }
        return tomcat;
    }

    private Tomcat getTomcat() {
        return tomcat;
    }

    @Fuzz
    public void processHTTPRequest(byte[] input) {

        try {
            Tomcat tomcat = getTomcat();
//            String request =
//                    "POST /echo-params.jsp HTTP/1.1" + "\r\n" +
//                            "Host: any" + "\r\n" +
//                            "Expect: unknown" +  "\r\n" +
//                            "\r\n";


            ProtocolHandler protocol = tomcat.getConnector().getProtocolHandler();
            AbstractHttp11Protocol<?> http11Protocol = (AbstractHttp11Protocol<?>) protocol;
            Http11Processor processor = new Http11Processor(http11Protocol, tomcat.getConnector().getProtocolHandler().getAdapter());
            ByteBuffer buf = ByteBuffer.wrap(input);
            processor.service(new SocketWrapper(buf));
        } catch(Exception e) {
            e.printStackTrace();
        }

    }

    @Fuzz
    public void parseHTTPRequestHeadersWithGenerator(@From(HTTPRequestGenerator.class)  @Dictionary("dictionaries/tomcat-http-request.dict")HttpUriRequest req) {
        try {
            String request = req.toString() + "\r\n";

            Header[] headerFields = req.getAllHeaders();
            for(int i = 0; i < headerFields.length; i++){
                request += (headerFields[i].getName() + ": " + headerFields[i].getValue() + "\r\n");
            }
            //System.out.print(request + "\r\n\r\n");
            processHTTPRequest(request.getBytes());
        } catch(Exception e) {
            Assume.assumeNoException(e);
        }
    }




    private static class TomcatWithFastSessionIDs extends Tomcat {

        @Override
        public void start() throws LifecycleException {
            // Use fast, insecure session ID generation for all tests
            Server server = getServer();
            for (Service service : server.findServices()) {
                Container e = service.getContainer();
                for (Container h : e.findChildren()) {
                    for (Container c : h.findChildren()) {
                        Manager m = ((Context) c).getManager();
                        if (m == null) {
                            m = new StandardManager();
                            ((Context) c).setManager(m);
                        }
                        if (m instanceof ManagerBase) {
                            ((ManagerBase) m).setSecureRandomClass(
                                    "org.apache.catalina.startup.FastNonSecureRandom");
                        }
                    }
                }
            }
            super.start();
        }
    }

        private static class SocketWrapper extends SocketWrapperBase<Void> {

            final ByteBuffer in;

            SocketWrapper(ByteBuffer in) {
                super(null, null);
                this.in = in;
                this.socketBufferHandler = new SocketBufferHandler(4096, 4096, true);
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
                throw new UnsupportedOperationException();
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


    }