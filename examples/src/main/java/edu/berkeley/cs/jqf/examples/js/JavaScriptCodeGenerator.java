package edu.berkeley.cs.jqf.examples.js;

import java.util.*;
import java.util.function.*;

import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.guidance.StringEqualsHintingInputStream;
import edu.columbia.cs.psl.phosphor.runtime.Taint;
import edu.columbia.cs.psl.phosphor.struct.LazyCharArrayObjTags;
import edu.columbia.cs.psl.phosphor.struct.TaintedObjectWithObjTag;
import edu.gmu.swe.knarr.runtime.ExpressionTaint;
import edu.gmu.swe.knarr.runtime.Symbolicator;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.FunctionCall;
import za.ac.sun.cs.green.expr.IntConstant;

/* Generates random strings that are syntactically valid JavaScript */
public class JavaScriptCodeGenerator extends Generator<String> {
    public JavaScriptCodeGenerator() {
        super(String.class); // Register type of generated object
    }

    private GenerationStatus status; // saved state object when generating
    private static final int MAX_IDENTIFIERS = 100;
    private static final int MAX_EXPRESSION_DEPTH = 10;
    private static final int MAX_STATEMENT_DEPTH = 6;
    private static Set<String> identifiers; // Stores generated IDs, to promote re-use
    private static List<String> identifiersList;
    private static Set<String> knownHints;
    static {
        if (System.getProperty("JSgeneratorReuseHints") != null)
            knownHints = new HashSet<>();
        else
            knownHints = new HashSet<String>(){
                @Override
                public boolean add(String s) {
                    return false;
                }

                @Override
                public boolean contains(Object o) {
                    return false;
                }
            };
    }
    private int statementDepth; // Keeps track of how deep the AST is at any point
    private int expressionDepth; // Keeps track of how nested an expression is at any point

    private static final String[] UNARY_TOKENS = {
            "!", "++", "--", "~",
            "delete", "new", "typeof"
    };

    private static final String[] BINARY_TOKENS = {
            "!=", "!==", "%", "%=", "&", "&&", "&=", "*", "*=", "+", "+=", ",",
            "-", "-=", "/", "/=", "<", "<<", ">>=", "<=", "=", "==", "===",
            ">", ">=", ">>", ">>=", ">>>", ">>>=", "^", "^=", "|", "|=", "||",
            "in", "instanceof"
    };

    /** Main entry point. Called once per test case. Returns a random JS program. */
    @Override
    public String generate(SourceOfRandomness random, GenerationStatus status) {
        this.status = status; // we save this so that we can pass it on to other generators
        this.identifiers = new HashSet<>();
        this.identifiersList = new ArrayList<>();
        this.identifiersList.addAll(knownHints);
        this.statementDepth = 0;
        this.expressionDepth = 0;
        return generateStatement(random).toString();
    }

    /** Utility method for generating a random list of items (e.g. statements, arguments, attributes) */
    private static List<String> generateItems(Function<SourceOfRandomness, String> genMethod, SourceOfRandomness random,
                                             int mean) {
        int len = random.nextInt(mean*2); // Generate random number in [0, mean*2) 
        List<String> items = new ArrayList<>(len);

        for (int i = 0; i < len; i++) {
            int choice = random.nextInt(0, Integer.MAX_VALUE);

            Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();
            String item;

            if (hints != null && hints.length > 0) {

                //random.nextInt(0, Integer.MAX_VALUE);
                choice = choice % hints.length;

                item = new String(hints[choice].getHint());
                StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
            } else {
                item = genMethod.apply(random);
            }

            item = applyTaints(item, choice);

            items.add(item);
        }
        return items;
    }

    /** Generates a random JavaScript statement */
    private String generateStatement(SourceOfRandomness random) {
        statementDepth++;
        String result;
        // If depth is too high, then generate only simple statements to prevent infinite recursion
        // If not, generate simple statements after the flip of a coin
        boolean coinFlip = false;
        int choice;
        if (statementDepth >= MAX_STATEMENT_DEPTH || (coinFlip = random.nextBoolean())) {
            // Choose a random private method from this class, and then call it with `random`
            switch (choice = random.nextInt(7)) {
                case 0:
                    result = this.generateExpressionStatement(random);
                    break;
                case 1:
                    result = this.generateBreakNode(random);
                    break;
                case 2:
                    result = this.generateContinueNode(random);
                    break;
                case 3:
                    result = this.generateReturnNode(random);
                    break;
                case 4:
                    result = this.generateThrowNode(random);
                    break;
                case 5:
                    result = this.generateVarNode(random);
                    break;
                default:
                    result = this.generateEmptyNode(random);
                    break;
            }
        } else {
            // If depth is low and we won the flip, then generate compound statements
            // (that is, statements that contain other statements)
            switch (choice = random.nextInt(7)) {
                case 0:
                    result = this.generateIfNode(random);
                    break;
                case 1:
                    result = this.generateForNode(random);
                    break;
                case 2:
                    result = this.generateWhileNode(random);
                    break;
                case 3:
                    result = this.generateNamedFunctionNode(random);
                    break;
                case 4:
                    result = this.generateSwitchNode(random);
                    break;
                case 5:
                    result = this.generateTryNode(random);
                    break;
                default:
                    result = this.generateBlock(random);
                    break;
            }
        }
        statementDepth--; // Reset statement depth when going up the recursive tree

//        result = applyTaints(result, choice);

        return result;
    }

//    private static String applyTaints(String result, Object taint) {
//        if (!(taint instanceof TaintedObjectWithObjTag))
//            return result;
//
//        String ret = new String(result);
//
//        if (Symbolicator.getTaints(result) instanceof LazyCharArrayObjTags) {
//            LazyCharArrayObjTags taints = (LazyCharArrayObjTags) Symbolicator.getTaints(result);
//            if (taints.taints != null)
//                for (int i = 0 ; i < taints.taints.length ; i++)
//                    taints.taints[i] = (taints.taints[i] == null ? ((Taint)((TaintedObjectWithObjTag)taint).getPHOSPHOR_TAG()) : taints.taints[i]);
//            else
//                taints.setTaints(((Taint)((TaintedObjectWithObjTag)taint).getPHOSPHOR_TAG()));
//        }
//
//        return ret;
//    }

    private static int currentFunctionNumber = 0;

    private static String applyTaints(String result, Object taint) {
        if (result == null || result.length() == 0 || !(taint instanceof TaintedObjectWithObjTag))
            return result;

        // New string to avoid adding taints to the dictionary itself
        String ret = new String(result);

        Expression t = (Expression) ((Taint)((TaintedObjectWithObjTag)taint).getPHOSPHOR_TAG()).getSingleLabel();

        if (Symbolicator.getTaints(result) instanceof LazyCharArrayObjTags) {
            LazyCharArrayObjTags taints = (LazyCharArrayObjTags) Symbolicator.getTaints(result);
            // Don't taint what's already tainted
            if (taints.taints != null)
                return result;

            taints.taints = new Taint[result.length()];
            for (int i = 0 ; i< taints.taints.length ; i++) {
                taints.taints[i] = new ExpressionTaint(new FunctionCall(
                        "gen" + currentFunctionNumber,
                        new Expression[]{ new IntConstant(i), t}));
            }

            currentFunctionNumber += 1;

        }

        // New string so that Phosphor can compute the tag for the string itself based on the tag for each character
        ret = new String(ret.getBytes(), 0, ret.length());

        return ret;
    }

    /** Generates a random JavaScript expression using recursive calls */
    private String generateExpression(SourceOfRandomness random) {
        expressionDepth++;
        String result;
        int choice;
        // Choose terminal if nesting depth is too high or based on a random flip of a coin
        if (expressionDepth >= MAX_EXPRESSION_DEPTH || random.nextBoolean()) {
            switch (choice = random.nextInt(2)) {
                case 0:
                    result = generateLiteralNode(random);
                    break;
                default:
                    result = generateIdentNode(random);
                    break;
            }
        } else {
            // Otherwise, choose a non-terminal generating function
            switch (choice = random.nextInt(8)) {
                case 0:
                    result = generateBinaryNode(random);
                    break;
                case 1:
                    result = generateUnaryNode(random);
                    break;
                case 2:
                    result = generateTernaryNode(random);
                    break;
                case 3:
                    result = generateCallNode(random);
                    break;
                case 4:
                    result = generateFunctionNode(random);
                    break;
                case 5:
                    result = generatePropertyNode(random);
                    break;
                case 6:
                    result = generateIndexNode(random);
                    break;
                default:
                    result = generateArrowFunctionNode(random);
                    break;
            }
        }
        expressionDepth--;

//        result = applyTaints(result, choice);

        return "(" + result + ")";
    }

    /** Generates a random binary expression (e.g. A op B) */
    private String generateBinaryNode(SourceOfRandomness random) {
        int choice = random.nextInt(0, BINARY_TOKENS.length);
        String token = new String(BINARY_TOKENS[choice]);
        String lhs = generateExpression(random);
        String rhs = generateExpression(random);

//        token = applyTaints(token, choice);

        return lhs + " " + token + " " + rhs;
    }

    /** Generates a block of statements delimited by ';' and enclosed by '{' '}' */
    private String generateBlock(SourceOfRandomness random) {
        return "{ " + String.join(";", generateItems(this::generateStatement, random, 4)) + " }";
    }

    private String generateBreakNode(SourceOfRandomness random) {
        return "break";
    }

    private String generateCallNode(SourceOfRandomness random) {
        String func;

        int choice = random.nextInt(0, Integer.MAX_VALUE);
        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();

        if (hints != null && hints.length > 0) {
            //random.nextInt(0, Integer.MAX_VALUE);
            choice = choice % hints.length;

            func = new String(hints[choice].getHint());
            StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
        } else {
            func = generateExpression(random);
        }

        func = applyTaints(func, choice);

        String args = String.join(",", generateItems(this::generateExpression, random, 3));

        String call = func + "(" + args + ")";
        if (random.nextBoolean()) {
            return call;
        } else {
            return "new " + call;
        }
    }

    private String generateCaseNode(SourceOfRandomness random) {
        return "case " + generateExpression(random) + ": " +  generateBlock(random);
    }

    private String generateCatchNode(SourceOfRandomness random) {
        return "catch (" + generateIdentNode(random) + ") " +
                generateBlock(random);
    }

    private String generateContinueNode(SourceOfRandomness random) {
        return "continue";
    }

    private String generateEmptyNode(SourceOfRandomness random) {
        return "";
    }

    private String generateExpressionStatement(SourceOfRandomness random) {
        return generateExpression(random);
    }

    private String generateForNode(SourceOfRandomness random) {
        String s = "for(";
        if (random.nextBoolean()) {
            s += generateExpression(random);
        }
        s += ";";
        if (random.nextBoolean()) {
            s += generateExpression(random);
        }
        s += ";";
        if (random.nextBoolean()) {
            s += generateExpression(random);
        }
        s += ")";
        s += generateBlock(random);
        return s;
    }

    private String generateFunctionNode(SourceOfRandomness random) {
        return "function(" + String.join(", ", generateItems(this::generateIdentNode, random, 5)) + ")" + generateBlock(random);
    }

    private String generateNamedFunctionNode(SourceOfRandomness random) {
        return "function " + generateIdentNode(random) + "(" + String.join(", ", generateItems(this::generateIdentNode, random, 5)) + ")" + generateBlock(random);
    }

    private String generateArrowFunctionNode(SourceOfRandomness random) {
        String params = "(" + String.join(", ", generateItems(this::generateIdentNode, random, 3)) + ")";
        boolean choice = random.nextBoolean();
        String result;
        if (choice) {
            result = params + " => " + generateBlock(random);
        } else {
            result = params + " => " + generateExpression(random);
        }

//        result = applyTaints(result, choice);

        return result;

    }

    private String generateIdentNode(SourceOfRandomness random) {
        // Either generate a new identifier or use an existing one
        String identifier;
        if (identifiers.isEmpty() || (identifiers.size() - knownHints.size() < MAX_IDENTIFIERS && random.nextBoolean())) {
            identifier = random.nextChar('a', 'z') + "_" + identifiers.size();
            identifiers.add(identifier);
            identifiersList.add(identifier);
        }

        boolean coin = random.nextBoolean();
        int choice = random.nextInt(0, Integer.MAX_VALUE);

        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();

        if (hints != null && hints.length > 0) {

            identifier = "";

            // This seems to work:  add all hints to a set that we use later to choose new identifiers from
            // This way, all hints that we found end up being used, even if at random places
            // It seems to improve coverage
            for (Coordinator.StringHint h : hints) {
                if (!knownHints.contains(h.getHint()))
                    knownHints.add(new String(h.getHint()));
            }

            //random.nextInt(0, Integer.MAX_VALUE);
            choice = choice % hints.length;

            identifier = new String(hints[choice].getHint());
            StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
        } else {
            choice = choice % identifiers.size();
            identifier = new String(identifiersList.get(choice));
        }

        identifier = applyTaints(identifier, choice);

        return identifier;
    }

    private String generateIfNode(SourceOfRandomness random) {
        return "if (" +
                generateExpression(random) + ") " +
                generateBlock(random) +
                (random.nextBoolean() ? generateBlock(random) : "");
    }

    private String generateIndexNode(SourceOfRandomness random) {
        return generateExpression(random) + "[" + generateExpression(random) + "]";
    }

    private String generateObjectProperty(SourceOfRandomness random) {
        return generateIdentNode(random) + ": " + generateExpression(random);
    }

    private String generateLiteralNode(SourceOfRandomness random) {
        // If we are not too deeply nested, then it is okay to generate array/object literals
        if (expressionDepth < MAX_EXPRESSION_DEPTH && random.nextBoolean()) {
            boolean choice = random.nextBoolean();
            String result;
            if (choice) {
                // Array literal
                result = "[" + String.join(", ", generateItems(this::generateExpression, random, 3)) + "]";
            } else {
                // Object literal
                result = "{" + String.join(", ", generateItems(this::generateObjectProperty, random, 3)) + "}";
            }

//            result = applyTaints(result, choice);

            return result;
        } else {
            // Otherwise, generate primitive literals
            int choice = random.nextInt(6);
            String result;
            switch (choice) {
                case 0:
                    result = String.valueOf(random.nextInt(-10, 1000)); // int literal
                    break;
                case 1:
                    result = String.valueOf(random.nextBoolean());      // bool literal
                    break;
                case 2:
                    result = generateStringLiteral(random);
                    break;
                case 3:
                    result = new String("undefined");
                    break;
                case 4:
                    result = new String("null");
                    break;
                default:
                    result = new String("this");
                    break;
            }

//            result = applyTaints(result, choice);

            return result;
        }
    }

    private String generateStringLiteral(SourceOfRandomness random) {
        // Generate an arbitrary string using the default string generator, and quote it
        return '"' + gen().type(String.class).generate(random, status) + '"';
    }

    private String generatePropertyNode(SourceOfRandomness random) {
        return generateExpression(random) + "." + generateIdentNode(random);
    }

    private String generateReturnNode(SourceOfRandomness random) {
        return random.nextBoolean() ? "return" : "return " + generateExpression(random);
    }

    private String generateSwitchNode(SourceOfRandomness random) {
        return "switch(" + generateExpression(random) + ") {"
                + String.join(" ", generateItems(this::generateCaseNode, random, 2)) + "}";
    }

    private String generateTernaryNode(SourceOfRandomness random) {
        return generateExpression(random) + " ? " + generateExpression(random) +
                " : " + generateExpression(random);
    }

    private String generateThrowNode(SourceOfRandomness random) {
        return "throw " + generateExpression(random);
    }

    private String generateTryNode(SourceOfRandomness random) {
        return "try " + generateBlock(random) + generateCatchNode(random);
    }

    private String generateUnaryNode(SourceOfRandomness random) {
        int choice = random.nextInt(UNARY_TOKENS.length);
        String token = new String(UNARY_TOKENS[choice]);

//        token = applyTaints(token, choice);

        return token + " " + generateExpression(random);
    }

    private String generateVarNode(SourceOfRandomness random) {
        return "var " + generateIdentNode(random);
    }

    private String generateWhileNode(SourceOfRandomness random) {
        return "while (" + generateExpression(random) + ")" + generateBlock(random);
    }
}
