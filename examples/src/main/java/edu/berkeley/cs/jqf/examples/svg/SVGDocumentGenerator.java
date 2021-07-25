package edu.berkeley.cs.jqf.examples.svg;


import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.generator.Size;
import com.pholser.junit.quickcheck.internal.GeometricDistribution;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import edu.berkeley.cs.jqf.examples.common.AlphaStringGenerator;
import edu.berkeley.cs.jqf.examples.common.Dictionary;
import edu.berkeley.cs.jqf.examples.common.DictionaryBackedStringGenerator;
import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.guidance.StringEqualsHintingInputStream;
import edu.berkeley.cs.jqf.fuzz.knarr.KnarrGuidance;
import edu.columbia.cs.psl.phosphor.runtime.Taint;
import edu.columbia.cs.psl.phosphor.struct.LazyCharArrayObjTags;
import edu.columbia.cs.psl.phosphor.struct.TaintedObjectWithObjTag;
import edu.gmu.swe.knarr.runtime.ExpressionTaint;
import edu.gmu.swe.knarr.runtime.Symbolicator;
import org.apache.batik.anim.dom.SVGDOMImplementation;
import org.junit.Assume;
import org.w3c.dom.*;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.FunctionCall;
import za.ac.sun.cs.green.expr.IntConstant;

import javax.xml.parsers.DocumentBuilderFactory;
import java.io.IOException;
import java.util.HashSet;



/**
 * A generator for SVG documents.
 *
 * @author James Kukucka
 */
public class SVGDocumentGenerator extends Generator<Document> {


    private static DocumentBuilderFactory documentBuilderFactory =
            DocumentBuilderFactory.newInstance();

    private static GeometricDistribution geometricDistribution =
            new GeometricDistribution();

    private static final String[] elements = {"a",
            "altGlyph",
            "altGlyphDef",
            "altGlyphItem",
            "animate",
            "animateColor",
            "animateMotion",
            "animateTransform",
            "circle",
            "clipPath",
            "color-profile",
            "cursor",
            "definition-src",
            "defs",
            "desc",
            "ellipse",
            "feBlend",
            "feColorMatrix",
            "feComponentTransfer",
            "feComposite",
            "feConvolveMatrix",
            "feDiffuseLighting",
            "feDisplacementMap",
            "feDistantLight",
            "feFlood",
            "feFuncA",
            "feFuncR",
            "feFuncG",
            "feFuncB",
            "feGaussianBlur",
            "feImage",
            "feMerge",
            "feMergeNode",
            "feMorphology",
            "feOffset",
            "fePointLight",
            "feSpecularLighting",
            "feSpotLight",
            "feTile",
            "feTurbulence",
            "filter",
            "font",
            "font-face",
            "font-face-format",
            "font-face-name",
            "font-face-src",
            "font-face-uri",
            "foreignObject",
            "g",
            "glyph",
            "glyphRef",
            "hkern",
            "image",
            "line",
            "linearGradient",
            "marker",
            "mask",
            "metadata",
            "missing-glyph",
            "mpath",
            "path",
            "pattern",
            "polygon",
            "polyline",
            "radialGradient",
            "rect",
            "set",
            "script",
            "stop",
            "style",
            "svg",
            "switch",
            "symbol",
            "text",
            "textPath",
            "title",
            "tref",
            "tspan",
            "use",
            "view",
            "vkern"};

    private HashSet<String> used_elements = new HashSet<>();

    /**
     * Mean number of child nodes for each XML element.
     */
    private static final double MEAN_NUM_CHILDREN = 4;

    /**
     * Mean number of attributes for each XML element.
     */
    private static final double MEAN_NUM_ATTRIBUTES = 2;

    /**
     * Minimum size of XML tree.
     *
     * @see {@link #configure(Size)}
     */
    private int minDepth = 0;

    /**
     * Maximum size of XML tree.
     *
     * @see {@link #configure(Size)}
     */
    private int maxDepth = 4;


    public SVGDocumentGenerator() {
        super(Document.class);
    }

    /**
     * Configures the minimum/maximum size of the SVG document.
     * <p>
     * This method is not usually invoked directly. Instead, use
     * the `@Size` annotation on fuzzed parameters to configure
     * automatically.
     *
     * @param size the min/max size of the XML document
     * @param size the min/max size of the XML document
     */
    public void configure(Size size) {
        minDepth = size.min();
        maxDepth = size.max();
    }


    private Generator<String> stringGenerator = new AlphaStringGenerator();


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

    private Document populateDocument(Document document, SourceOfRandomness random, GenerationStatus status) {
        String svgNS = SVGDOMImplementation.SVG_NAMESPACE_URI;
        Element root = document.getDocumentElement();
        Element new_element = document.createElementNS(svgNS, elements[random.nextInt(0, elements.length)]);
        populateElement(document, new_element, random, status, 0);
        root.appendChild(new_element);
        return document;
    }

    @Override
    public Document generate(SourceOfRandomness sourceOfRandomness, GenerationStatus generationStatus) {
        DOMImplementation impl = SVGDOMImplementation.getDOMImplementation();
        String svgNS = SVGDOMImplementation.SVG_NAMESPACE_URI;
        Document doc = impl.createDocument(svgNS, "svg", null);

        try {
            populateDocument(doc, sourceOfRandomness, generationStatus);
        } catch (DOMException e) {
            Assume.assumeNoException(e);
        }
        return doc;
    }

    private String makeString(SourceOfRandomness random, GenerationStatus status) {

        int choice = random.nextInt(0, Integer.MAX_VALUE);
        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();
        String word;

        if (hints != null && hints.length > 0 ) {
            choice = choice % hints.length;
            word = hints[choice].getHint();
        } else {
            word = stringGenerator.generate(random, status);
        }

        word = applyTaints(word, choice);

        return word;
    }

    private void populateElement(Document document, Element elem, SourceOfRandomness random, GenerationStatus status, int depth) {

        // Make children
        String svgNS = SVGDOMImplementation.SVG_NAMESPACE_URI;
        if (depth < minDepth || (depth < maxDepth && random.nextBoolean())) {
            int numChildren = Math.max(0, geometricDistribution.sampleWithMean(MEAN_NUM_CHILDREN, random) - 1);
            for (int i = 0; i < numChildren; i++) {

                int choice = random.nextInt(0, Integer.MAX_VALUE);
                Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();
                String word;
                if (hints != null && hints.length > 0 ) {
                    choice = choice % hints.length;
                    word = hints[choice].getHint();
                } else {
                    word = elements[choice % elements.length];
                }

                word = applyTaints(word, choice);

                Element child = document.createElementNS(svgNS, word);
                populateElement(document, child, random, status, depth + 1);
                elem.appendChild(child);
            }
        } else if (random.nextBoolean()) {
            // Add text
            Text text = document.createTextNode(makeString(random, status));
            elem.appendChild(text);
        }
    }

    private static int currentFunctionNumber = 0;

    private static String applyTaints(String result, Object taint) {
        if (result == null || result.length() == 0 || !(taint instanceof TaintedObjectWithObjTag))
            return result;


        // New string to avoid adding taints to the dictionary itself
        String ret = new String(result);

        Expression t = (Expression) ((Taint)((TaintedObjectWithObjTag)taint).getPHOSPHOR_TAG()).getSingleLabel();

        if (Symbolicator.getTaints(result) instanceof LazyCharArrayObjTags) {
            LazyCharArrayObjTags taints = (LazyCharArrayObjTags) Symbolicator.getTaints(result);
            taints.taints = new Taint[result.length()];
            for (int i = 0 ; i< taints.taints.length ; i++) {
                taints.taints[i] = new ExpressionTaint(new FunctionCall(
                        "gen" + currentFunctionNumber,
                        new Expression[]{ new IntConstant(i), t}));
            }
            KnarrGuidance.generatedStrings.put("gen"+currentFunctionNumber, result);
            currentFunctionNumber += 1;

        }

        // New string so that Phosphor can compute the tag for the string itself based on the tag for each character
        ret = new String(ret.getBytes(), 0, ret.length());

        return ret;
    }

}
