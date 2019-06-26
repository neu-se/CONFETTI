package edu.berkeley.cs.jqf.examples.tomcat;

import org.apache.catalina.LifecycleState;

import org.apache.catalina.connector.Connector;

import org.apache.catalina.startup.Tomcat;

import org.apache.coyote.http11.Http11NioProtocol;

import org.apache.http.HttpEntity;

import org.apache.http.client.methods.CloseableHttpResponse;

import org.apache.http.client.methods.HttpUriRequest;

import org.apache.http.client.utils.URIBuilder;

import org.apache.http.impl.client.CloseableHttpClient;

import org.apache.http.impl.client.HttpClientBuilder;

import org.apache.http.util.EntityUtils;


import org.junit.Before;
import org.junit.Rule;

import org.junit.rules.ExternalResource;

import javax.servlet.ServletException;

import java.io.File;

import java.io.IOException;

import java.net.InetAddress;

import java.util.HashSet;

import java.util.logging.*;

import static org.junit.Assert.assertEquals;

public abstract class TomcatBaseTest  {

    protected static Tomcat tomcat = null;

    private static final String baseDir = "tomcat";

    //private static final String webappDir = "/home/jamesk/Documents/jqf-artifact/software/jqf/examples-inst/apache-tomcat-8.0.47/webapps"; //".." + File.separator + "struts-2.3.37" + File.separator + "apps";
    private static final String webappDir = "/home/jamesk/Documents/jqf-artifact/software/jqf/examples/apache-tomcat-8.0.47/webapps"; //".." + File.separator + "struts-2.3.37" + File.separator + "apps";

    private static final String  instrumentedWebappDir= "/home/jamesk/Documents/jqf-artifact/software/jqf/examples-inst/apache-tomcat-8.0.47/webapps";
    private static final HashSet<String> addedWebapps = new HashSet<>();

//
//    @Before
//    public void before() throws Throwable {
//        System.out.println("Before");
//        if(tomcat == null) {
//
//            // Setup the embedded server
//
//            tomcat = new Tomcat();
//
//            tomcat.setBaseDir(baseDir);
//
//            tomcat.getHost().setAppBase(baseDir);
//
//            String protocol = Http11NioProtocol.class.getName();
//
//            Connector connector = new Connector(protocol);
//
//            // Listen on localhost
//
//            connector.setAttribute("address", InetAddress.getByName("localhost").getHostAddress());
//
//            // Use a random free port
//
//            connector.setPort(0);
//
//            tomcat.getService().addConnector(connector);
//
//            tomcat.setConnector(connector);
//
//            tomcat.setSilent(true);
//
//            tomcat.getHost().setDeployOnStartup(true);
//
//            tomcat.getHost().setAutoDeploy(true);
//
//            replaceRootLoggerHandlers();
//
//            tomcat.init();
//
//            tomcat.start();
//
//            addWebApp("struts2-showcase-2_3_20_1");
//
//            // Add the shutdown hook to stop the embedded server
//
//            Runnable shutdown = new Runnable() {
//
//                @Override
//
//                public void run() {
//
//                    try {
//
//                        try {
//
//                            // Stop and destroy the server
//
//                            if(tomcat.getServer() != null && tomcat.getServer().getState() != LifecycleState.DESTROYED) {
//
//                                if (tomcat.getServer().getState() != LifecycleState.STOPPED) {
//
//                                    tomcat.stop();
//
//                                }
//
//                                tomcat.destroy();
//
//                                tomcat = null;
//
//                            }
//
//                        } finally {
//
//                            // Delete tomcat's temporary working directory
//
//
//
//                        }
//
//                    } catch(Throwable t) {
//
//                        t.printStackTrace();
//
//                    }
//
//                }
//
//            };
//
//            Runtime.getRuntime().addShutdownHook(new Thread(shutdown));
//
//        }
//
//    }

    @Rule
    public final ExternalResource resource = new ExternalResource() {

        @Override

        protected void before() throws Throwable {
            System.out.println("Before");
            if(tomcat == null) {

                // Setup the embedded server

                tomcat = new Tomcat();

                tomcat.setBaseDir(baseDir);

                tomcat.getHost().setAppBase(baseDir);

                String protocol = Http11NioProtocol.class.getName();

                Connector connector = new Connector(protocol);

                // Listen on localhost

                connector.setAttribute("address", InetAddress.getByName("localhost").getHostAddress());

                // Use a random free port

                connector.setPort(0);


                tomcat.getService().addConnector(connector);

                tomcat.setConnector(connector);

                tomcat.setSilent(true);

                tomcat.getHost().setDeployOnStartup(true);

                tomcat.getHost().setAutoDeploy(true);

                replaceRootLoggerHandlers();

                tomcat.init();

                tomcat.start();

                // Add the shutdown hook to stop the embedded server

                Runnable shutdown = new Runnable() {

                    @Override

                    public void run() {

                        try {

                            try {

                                // Stop and destroy the server

                                if(tomcat.getServer() != null && tomcat.getServer().getState() != LifecycleState.DESTROYED) {

                                    if (tomcat.getServer().getState() != LifecycleState.STOPPED) {

                                        tomcat.stop();

                                    }

                                    tomcat.destroy();

                                    tomcat = null;

                                }

                            } finally {

                                // Delete tomcat's temporary working directory



                            }

                        } catch(Throwable t) {

                            t.printStackTrace();

                        }

                    }

                };

                Runtime.getRuntime().addShutdownHook(new Thread(shutdown));

            }

        }

    };

    /* Returns a newly created file handler with the specified logging level that logs to a file in the base tomcat directory. */

    private static Handler createFileHandler() throws IOException {

        // Ensure that the base directory exists

        File baseDirFile = new File(baseDir);

        if(!baseDirFile.isDirectory() && !baseDirFile.mkdirs()) {

            System.err.println("Failed to make base directory for embedded tomcat.");

        }

        Handler fileHandler = new FileHandler(baseDir + File.separator + "catalina.out", true);

        fileHandler.setFormatter(new SimpleFormatter());

        fileHandler.setLevel(Level.INFO);

        fileHandler.setEncoding("UTF-8");

        return fileHandler;

    }

    /* Removes any existing handlers for the specified logger and adds the specified handler. */

    private static void replaceRootLoggerHandlers() throws IOException {

        Logger rootLogger = LogManager.getLogManager().getLogger("");

        rootLogger.setUseParentHandlers(false);

        // Change the level of any existing handlers to SEVERE

        for(Handler h : rootLogger.getHandlers()) {

            h.setLevel(Level.SEVERE);

        }

        // Add a file handler for INFO level logging

        rootLogger.addHandler(createFileHandler());

    }

    /* Adds the webapp with the specified name if has not already been added to the embedded server. */

    public static void addWebApp(String name) throws ServletException  {

        if(addedWebapps.add(name)) {

            if(System.getenv("KNARR_EXEC") == null)
                tomcat.addWebapp("/" + name, new File(webappDir + File.separator + name).getAbsolutePath());
            else
                tomcat.addWebapp("/" + name, new File(instrumentedWebappDir + File.separator + name).getAbsolutePath());

        }

    }

    /* Returns a URIBuilder with the base components for making requests to the embedded server set. */

    public static URIBuilder getBaseURIBuilder() {

        return new URIBuilder()

                .setScheme("http")

                .setHost(tomcat.getHost().getName())

                .setPort(tomcat.getConnector().getLocalPort());

    }

    /* Executes the specified request and returns the contents of the response. */

    public String makeRequest(HttpUriRequest request) throws Exception {

        return makeRequest(request, -1, false);

    }

    /* Executes the specified request and asserts that the resulting response has the specified status code. Returns the

     * contents of the response. */

    public String makeRequest(HttpUriRequest request, int statusCode) throws Exception {

        return makeRequest(request, statusCode, true);

    }

    /* Executes the specified request and asserts that the resulting response has the specified status code if checkStatus

     * is true. Returns the contents of the response. */

    private String makeRequest(HttpUriRequest request, int statusCode, boolean checkStatus) throws Exception {

        String result = null;

        CloseableHttpClient client = HttpClientBuilder.create().build();

        try (CloseableHttpResponse response = client.execute(request)) {

            HttpEntity entity = response.getEntity();

            if (entity != null) {

                if (entity.getContentLength() != -1) {

                    result = EntityUtils.toString(entity);

                }

            }

            if(checkStatus) {

                // Reruns may fail status check

                assertEquals(statusCode, response.getStatusLine().getStatusCode());

            }

            EntityUtils.consume(entity);

        } catch(Exception e) {
             throw e;
        }

        return result;

    }

}

