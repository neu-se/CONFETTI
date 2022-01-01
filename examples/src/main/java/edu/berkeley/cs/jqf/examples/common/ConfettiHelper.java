package edu.berkeley.cs.jqf.examples.common;

import edu.berkeley.cs.jqf.fuzz.central.Coordinator;
import edu.berkeley.cs.jqf.fuzz.ei.ZestGuidance;
import edu.berkeley.cs.jqf.fuzz.extendedDictionary.ExtendedDictionaryEvaluatorGuidance;
import edu.berkeley.cs.jqf.fuzz.guidance.RecordingInputStream;
import edu.berkeley.cs.jqf.fuzz.guidance.StringEqualsHintingInputStream;
import edu.berkeley.cs.jqf.fuzz.knarr.KnarrGuidance;
import edu.columbia.cs.psl.phosphor.PreMain;
import edu.columbia.cs.psl.phosphor.runtime.Taint;
import edu.columbia.cs.psl.phosphor.struct.LazyCharArrayObjTags;
import edu.columbia.cs.psl.phosphor.struct.TaintedObjectWithObjTag;
import edu.gmu.swe.knarr.runtime.ExpressionTaint;
import edu.gmu.swe.knarr.runtime.Symbolicator;
import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.expr.FunctionCall;
import za.ac.sun.cs.green.expr.IntConstant;

import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ConfettiHelper {
    private static final Set<String> globalDictionarySet = new HashSet<>();
    private static final List<String> globalDictionary = new ArrayList<>();

    public static void clearGlobalDictionary(){
        globalDictionary.clear();
        globalDictionarySet.clear();
    }

    public static void excludeFromGlobalDictionary(String val){
        globalDictionarySet.add(val);
    }

    /**
     * Allows a generator to use some pre-determined string (not necessarily from a dictionary), but still
     * potentially apply hints at this string.
     */
    public static String chooseString(int choice, boolean useExtendedDict, String stringToUse){
        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();
        int[] pos = new int[]{RecordingInputStream.unsafeGetLastMark()-4,4};

        String ret = stringToUse;
        if (useExtendedDict) {
            if (globalDictionary.size() == 0) {
                ret = stringToUse;
            } else {
                choice = choice % globalDictionary.size();
                ret = globalDictionary.get(choice);
                if(ZestGuidance.currentInput != null)
                    ZestGuidance.currentInput.numGlobalDictionaryHintsApplied++;
            }
            if(ZestGuidance.currentInput != null) {
                ZestGuidance.currentInput.addSingleHintInPlace(
                        new Coordinator.StringHint(ret, Coordinator.HintType.GLOBAL_DICTIONARY, null), pos);
            }
        } else if (hints != null && hints.length > 0 ) {
            choice = choice % hints.length;
            ret = new String(hints[choice].getHint());
            if (!PreMain.RUNTIME_INST && !ZestGuidance.IGNORE_GLOBAL_DICTIONARY && globalDictionarySet.add(ret)) {
                globalDictionary.add(ret);
                ZestGuidance.extendedDictionarySize++;
            }
            StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
        }
        return applyTaints(ret, choice);
    }

    /**
     * Sometimes a generator might want to make some calls between picking the random choice and
     * generating a string. This doesn't seem like a great generator design (why not move the random choice to pick your string
     * to the decision point where you actually pick it?) but we didn't want to change the logic of existing
     * generators. This variant of chooseFromDictionary allows the genreator to pass the expected set of hints, rather than
     * assuming that the hints are lined up and ready to go at the call to this helper function
     *
     */
    public static String chooseFromDictionaryOrUseDefault(int choice, boolean useExtendedDict, boolean useDefault, String def, String[] dictionary, Coordinator.StringHint[] hints){
        String ret = def;
        if (hints != null && hints.length > 0 ) {
            //random.nextInt(0, Integer.MAX_VALUE);
            choice = choice % hints.length;

            ret = new String(hints[choice].getHint());
            StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
        }
        else if (useDefault) {
            choice = choice % (dictionary.length + (useExtendedDict ? globalDictionary.size() : 0));
            RecordingInputStream.unsafePatchLastReadIntTo(choice);
            if(choice < dictionary.length)
                ret =  dictionary[choice % dictionary.length];
            else{
                int[] pos = new int[]{RecordingInputStream.unsafeGetLastMark()-4,4};
                ret = globalDictionary.get(choice - dictionary.length);
                if(ZestGuidance.currentInput != null) {
                    ZestGuidance.currentInput.addSingleHintInPlace(
                            new Coordinator.StringHint(ret, Coordinator.HintType.GLOBAL_DICTIONARY, null), pos);
                    ZestGuidance.currentInput.numGlobalDictionaryHintsApplied++;
                }
            }
        }
        return applyTaints(ret, choice);

    }

    public static String chooseFromDictionary(int choice, boolean useExtendedDict, String[] dictionary) {
        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();

        String word = "";
        if (hints != null && hints.length > 0) {
            word = hints[0].getHint();
            if (hints[0].getType() == Coordinator.HintType.INDEXOF) {
                String origWord = dictionary[(choice % dictionary.length)];
                if (origWord.length() <= 1) {
                    word = origWord + word;
                } else {
                    int middle = origWord.length() / 2;
                    word = origWord.substring(0, middle) + word + origWord.substring(middle);
                }
            }
            if (!PreMain.RUNTIME_INST && !ZestGuidance.IGNORE_GLOBAL_DICTIONARY && globalDictionarySet.add(word)) {
                ZestGuidance.extendedDictionarySize++;
                globalDictionary.add(word);
            }

            if (hints[0].getType() == Coordinator.HintType.Z3) {
                StringEqualsHintingInputStream.z3HintsUsedInCurrentInput = true;
            }
            StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
        } else {
            choice = choice % (dictionary.length + (useExtendedDict ? globalDictionary.size() : 0));
            RecordingInputStream.unsafePatchLastReadIntTo(choice);
            if(choice < dictionary.length) {
                word = dictionary[choice];
            } else{
                int[] pos = new int[]{RecordingInputStream.unsafeGetLastMark()-4,4};
                word = globalDictionary.get(choice - dictionary.length);
                if(ZestGuidance.currentInput != null) {
                    ZestGuidance.currentInput.addSingleHintInPlace(
                            new Coordinator.StringHint(word, Coordinator.HintType.GLOBAL_DICTIONARY, null), pos);
                    ZestGuidance.currentInput.numGlobalDictionaryHintsApplied++;
                }
            }
        }
        return applyTaints(word, choice);
    }

    public static String chooseFromDictionary(int choice, boolean useExtendedDict, List<String> dictionary) {
        Coordinator.StringHint[] hints = StringEqualsHintingInputStream.getHintsForCurrentInput();

        String word = "";
        if (hints != null && hints.length > 0) {
            word = hints[0].getHint();
            if (hints[0].getType() == Coordinator.HintType.INDEXOF) {
                String origWord = dictionary.get(choice % dictionary.size());
                if (origWord.length() <= 1) {
                    word = origWord + word;
                } else {
                    int middle = origWord.length() / 2;
                    word = origWord.substring(0, middle) + word + origWord.substring(middle);
                }
            }
            if (!PreMain.RUNTIME_INST && !ZestGuidance.IGNORE_GLOBAL_DICTIONARY && globalDictionarySet.add(word)) {
                ZestGuidance.extendedDictionarySize++;
                globalDictionary.add(word);
            }

            if (hints[0].getType() == Coordinator.HintType.Z3) {
                StringEqualsHintingInputStream.z3HintsUsedInCurrentInput = true;
            }
            StringEqualsHintingInputStream.hintUsedInCurrentInput = true;
        } else {
            choice = choice % (dictionary.size() + (useExtendedDict ? globalDictionary.size() : 0));
            RecordingInputStream.unsafePatchLastReadIntTo(choice);
            if(choice < dictionary.size()) {
                word = dictionary.get(choice);
            } else{
                int[] pos = new int[]{RecordingInputStream.unsafeGetLastMark()-4,4};
                word = globalDictionary.get(choice - dictionary.size());
                if(ZestGuidance.currentInput != null) {
                    ZestGuidance.currentInput.addSingleHintInPlace(
                            new Coordinator.StringHint(word, Coordinator.HintType.GLOBAL_DICTIONARY, null), pos);
                    ZestGuidance.currentInput.numGlobalDictionaryHintsApplied++;
                }
            }
        }
        return applyTaints(word, choice);
    }

    private static int currentFunctionNumber = 0;

    private static String applyTaints(String result, Object taint) {
        if (!PreMain.RUNTIME_INST)
            ExtendedDictionaryEvaluatorGuidance.generatedStrings++;
        if (result == null || result.length() == 0 || !(taint instanceof TaintedObjectWithObjTag))
            return result;


        // New string to avoid adding taints to the dictionary itself
        String ret = new String(result.getBytes(), 0, result.length());

        Expression t = (Expression) ((Taint) ((TaintedObjectWithObjTag) taint).getPHOSPHOR_TAG()).getSingleLabel();

        if (Symbolicator.getTaints(ret) instanceof LazyCharArrayObjTags) {
            LazyCharArrayObjTags taints = (LazyCharArrayObjTags) Symbolicator.getTaints(ret);
            taints.taints = new Taint[ret.length()];
            for (int i = 0; i < taints.taints.length; i++) {
                taints.taints[i] = new ExpressionTaint(new FunctionCall(
                        "gen" + currentFunctionNumber,
                        new Expression[]{new IntConstant(i), t}));
            }
            KnarrGuidance.generatedStrings.put("gen" + currentFunctionNumber, ret);
            currentFunctionNumber += 1;
        }

        // New string so that Phosphor can compute the tag for the string itself based on the tag for each character
        ret = new String(ret.getBytes(), 0, ret.length());

        return ret;
    }
}
