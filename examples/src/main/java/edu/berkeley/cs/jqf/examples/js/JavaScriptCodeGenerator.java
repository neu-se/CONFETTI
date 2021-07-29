package edu.berkeley.cs.jqf.examples.js;

import java.util.*;
import java.util.function.*;

import com.pholser.junit.quickcheck.generator.GenerationStatus;
import com.pholser.junit.quickcheck.generator.Generator;
import com.pholser.junit.quickcheck.random.SourceOfRandomness;
import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.guidance.StringEqualsHintingInputStream;
import edu.berkeley.cs.jqf.fuzz.knarr.KnarrGuidance;
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
    private int statementDepth; // Keeps track of how deep the AST is at any point
    private int expressionDepth; // Keeps track of how nested an expression is at any point

    // The original generator created identifiers *as it went*
    // This was a nice idea in theory, because you would start out making expressions with the same identifier a lot
    // But, it totally, totally, totally destroys any determinism of the generator: same seed will result in a different
    // identifier, and even worse, it would actually result in a totally different input (since generating an identifier
    // would consume some random bytes that could have gone somewhere else.
    // These hardcoded identifiers were generated the exact same way that they would have been anyway.
    // - JSB
    private static final String[] IDENTIFIERS = {"z_0", "m_1", "r_2", "e_3", "r_4", "l_5", "h_6", "p_7", "y_8", "r_9", "t_10", "u_11", "s_12", "x_13", "l_14", "t_15", "s_16", "m_17", "r_18", "j_19", "i_20", "q_21", "g_22", "n_23", "y_24", "t_25", "o_26", "q_27", "v_28", "d_29", "b_30", "n_31", "j_32", "g_33", "w_34", "t_35", "z_36", "t_37", "h_38", "r_39", "l_40", "b_41", "d_42", "r_43", "o_44", "i_45", "a_46", "p_47", "x_48", "b_49", "t_50", "h_51", "z_52", "q_53", "b_54", "a_55", "h_56", "m_57", "w_58", "o_59", "y_60", "w_61", "p_62", "d_63", "v_64", "d_65", "u_66", "i_67", "w_68", "x_69", "i_70", "a_71", "t_72", "b_73", "b_74", "d_75", "s_76", "a_77", "w_78", "q_79", "x_80", "n_81", "u_82", "g_83", "s_84", "l_85", "n_86", "j_87", "q_88", "x_89", "q_90", "r_91", "c_92", "m_93", "e_94", "t_95", "i_96", "l_97", "g_98", "x_99", };


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
            String item;
                item = genMethod.apply(random);
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
        String ret = new String(result.getBytes(), 0, result.length());

        Expression t = (Expression) ((Taint)((TaintedObjectWithObjTag)taint).getPHOSPHOR_TAG()).getSingleLabel();

        if (Symbolicator.getTaints(ret) instanceof LazyCharArrayObjTags) {
            LazyCharArrayObjTags taints = (LazyCharArrayObjTags) Symbolicator.getTaints(ret);
            // Don't taint what's already tainted
            if (taints.taints != null)
                return result;

            taints.taints = new Taint[ret.length()];
            for (int i = 0 ; i< taints.taints.length ; i++) {
                taints.taints[i] = new ExpressionTaint(new FunctionCall(
                        "gen" + currentFunctionNumber,
                        new Expression[]{ new IntConstant(i), t}));
            }
            KnarrGuidance.generatedStrings.put("gen"+currentFunctionNumber, ret);
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
        int choice = random.nextInt(0, Integer.MAX_VALUE);

        String token;
        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();
        if (hints != null && hints.length > 0 ) {
            token = new String(hints[0].getHint());
            StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
        } else {
            choice = choice % BINARY_TOKENS.length;
            token = new String(BINARY_TOKENS[choice]);
        }
        token = applyTaints(token, choice);

        String lhs = generateExpression(random);
        String rhs = generateExpression(random);

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

        func = generateExpression(random);

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

        return result;

    }

    private String generateIdentNode(SourceOfRandomness random) {
        // Either generate a new identifier or use an existing one
        String identifier;
        //if (identifiers.isEmpty() || (identifiers.size() - knownHints.size() < MAX_IDENTIFIERS && random.nextBoolean())) {
        //    identifier = random.nextChar('a', 'z') + "_" + identifiers.size();
        //    identifiers.add(identifier);
        //    identifiersList.add(identifier);
        //}

        int choice = random.nextInt(0, Integer.MAX_VALUE);

        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();
        if (hints != null && hints.length > 0 ) {
            identifier = new String(hints[0].getHint());
            StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
        } else {
            choice = choice % IDENTIFIERS.length;
            identifier = new String(IDENTIFIERS[choice]);
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
        // todo will we use hints here!?!?
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
        int choice = random.nextInt(0, Integer.MAX_VALUE);

        String token;
        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();
        if (hints != null && hints.length > 0 ) {
            token = new String(hints[0].getHint());
            StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
        } else {
            choice = choice % UNARY_TOKENS.length;
            token = new String(UNARY_TOKENS[choice]);
        }

        token = applyTaints(token, choice);

        return token + " " + generateExpression(random);
    }

    private String generateVarNode(SourceOfRandomness random) {
        return "var " + generateIdentNode(random);
    }

    private String generateWhileNode(SourceOfRandomness random) {
        return "while (" + generateExpression(random) + ")" + generateBlock(random);
    }
}
