/*
 * Copyright (c) 2017-2018 The Regents of the University of California
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package edu.berkeley.cs.jqf.examples.ant;

import java.io.*;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Files;
import java.nio.file.Path;

import com.pholser.junit.quickcheck.From;
import edu.berkeley.cs.jqf.examples.xml.XMLDocumentUtils;
import edu.berkeley.cs.jqf.examples.xml.XmlDocumentGenerator;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.fuzz.Fuzz;
import edu.berkeley.cs.jqf.fuzz.JQF;
import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.Location;
import org.apache.tools.ant.Project;
import org.apache.tools.ant.helper.ProjectHelperImpl;
import org.apache.tools.ant.util.FileUtils;
import org.apache.tools.ant.util.JAXPUtils;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.w3c.dom.Document;
import org.xml.sax.HandlerBase;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;
import org.xml.sax.helpers.XMLReaderAdapter;

@RunWith(JQF.class)
public class ProjectBuilderTest {

    private File serializeInputStream(InputStream in) throws IOException {
        Path path = Files.createTempFile("build", ".xml");
        try (BufferedWriter out = Files.newBufferedWriter(path)) {
            int b;
            while ((b = in.read()) != -1) {
                out.write(b);
            }
        }
        return path.toFile();
    }

    @Fuzz
    public void testWithInputStream(InputStream in) {
        File buildXml = null;
        try {
            ProjectHelperImpl p = new MyProjectHelperImpl();
            p.parse(new Project(), in);
        } catch (BuildException e) {
            Assume.assumeNoException(e);
        } finally {
            if (buildXml != null) {
                buildXml.delete();
            }
        }
    }

    @Fuzz
    public void testWithGenerator(@From(XmlDocumentGenerator.class)
                                      @Dictionary("dictionaries/ant-project.dict") Document dom) {
        testWithInputStream(XMLDocumentUtils.documentToInputStream(dom));
    }


    @Fuzz
    public void testWithGeneratorEmptyDictionary(@From(XmlDocumentGenerator.class)
                                  @Dictionary("dictionaries/empty.dict") Document dom) {
        testWithInputStream(XMLDocumentUtils.documentToInputStream(dom));
    }
    @Fuzz
    public void testWithGeneratorNoDictionary(@From(XmlDocumentGenerator.class) Document dom) {
        testWithInputStream(XMLDocumentUtils.documentToInputStream(dom));
    }

    @Fuzz
    public void debugWithGenerator(@From(XmlDocumentGenerator.class)
                                       @Dictionary("dictionaries/ant-project.dict") Document dom) {
        System.out.println(XMLDocumentUtils.documentToString(dom));
        testWithGenerator(dom);
    }

    @Fuzz
    public void testWithString(String input) throws BuildException {
        testWithInputStream(new ByteArrayInputStream(input.getBytes()));
    }

    @Test
    public void testSmall() throws BuildException {
        testWithString("<project default='s' />");
    }

    private static class MyProjectHelperImpl extends ProjectHelperImpl {

        @Override
        public void parse(Project project, Object source) throws BuildException {
            if (source instanceof InputStream) {

                InputStream inputStream = (InputStream) source;
                InputSource inputSource = null;

                org.xml.sax.Parser parser;

                try {
                    try {
                        parser = JAXPUtils.getParser();
                    } catch (BuildException e) {
                        parser = new XMLReaderAdapter(JAXPUtils.getXMLReader());
                    }
                    inputSource = new InputSource(inputStream);
                    HandlerBase hb; // = new RootHandler(this);
                    try {
                        Class<?> c = Class.forName(ProjectHelperImpl.class.getName() + "$RootHandler");
                        Constructor<?> cc = c.getDeclaredConstructor(ProjectHelperImpl.class);
                        cc.setAccessible(true);
                        hb = (HandlerBase) cc.newInstance(this);

                        {
                            Field f = ProjectHelperImpl.class.getDeclaredField("parser");
                            f.setAccessible(true);
                            f.set(this, parser);
                        }
                        {
                            Field f = ProjectHelperImpl.class.getDeclaredField("project");
                            f.setAccessible(true);
                            f.set(this, project);
                        }
                        {
                            Field f = ProjectHelperImpl.class.getDeclaredField("buildFile");
                            f.setAccessible(true);
                            f.set(this, new File("/tmp/build.xml"));
                        }
                        {
                            Field f = ProjectHelperImpl.class.getDeclaredField("buildFileParent");
                            f.setAccessible(true);
                            f.set(this, new File("/tmp"));
                        }
                    } catch (ClassNotFoundException | NoSuchMethodException | InstantiationException | IllegalAccessException | InvocationTargetException | NoSuchFieldException e) {
                        throw new Error(e);
                    }
                    parser.setDocumentHandler(hb);
                    parser.setEntityResolver(hb);
                    parser.setErrorHandler(hb);
                    parser.setDTDHandler(hb);
                    parser.parse(inputSource);
                } catch (SAXParseException exc) {
                    Location location = new Location(exc.getSystemId(), exc.getLineNumber(), exc
                            .getColumnNumber());

                    Throwable t = exc.getException();
                    if (t instanceof BuildException) {
                        BuildException be = (BuildException) t;
                        if (be.getLocation() == Location.UNKNOWN_LOCATION) {
                            be.setLocation(location);
                        }
                        throw be;
                    }
                    throw new BuildException(exc.getMessage(), t, location);
                } catch (SAXException exc) {
                    Throwable t = exc.getException();
                    if (t instanceof BuildException) {
                        throw (BuildException) t;
                    }
                    throw new BuildException(exc.getMessage(), t);
                } catch (FileNotFoundException exc) {
                    throw new BuildException(exc);
                } catch (UnsupportedEncodingException exc) {
                    throw new BuildException("Encoding of project file is invalid.", exc);
                } catch (IOException exc) {
                    throw new BuildException("Error reading project file: " + exc.getMessage(), exc);
                } finally {
                    FileUtils.close(inputStream);
                }
            } else {
                super.parse(project, source);
            }
        }
    }
}
