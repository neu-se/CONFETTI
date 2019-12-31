package edu.berkeley.cs.jqf.fuzz.central;


import com.pholser.junit.quickcheck.Pair;

import java.util.ArrayList;

import java.util.HashMap;
import java.util.LinkedList;

public class Z3InputHints {

    private static final Z3InputHints instance = new Z3InputHints();

    private HashMap<Integer, LinkedList<Z3StringHint>> hints;

    private Z3InputHints()
    {
         this.hints = new HashMap<>();
    }

    private Boolean hasHints() { return !hints.isEmpty(); }

    private LinkedList<Z3StringHint> getHintsByInputId(Integer inputId) {
        return this.hints.get(inputId);
    }

    public  LinkedList<Z3StringHint> getHints() {
        if(this.hasHints()) {
            return this.hints.remove(new ArrayList<Integer>(this.hints.keySet()).get(0));
        } else {
            return null;
        }
    }

    public void addHint(Integer inputId, Pair<String, String> hint) {
        Z3StringHint z3StringHint = new Z3StringHint(inputId, hint);
        // We already have at least one hint for this inputID
        if(this.hints.containsKey(inputId)) {
            this.hints.get(inputId).add(z3StringHint);
        }
        else {
            LinkedList<Z3StringHint> inputHintList = new LinkedList<>();
            inputHintList.add(z3StringHint);
            this.hints.put(inputId, inputHintList);
        }
    }


    public static Z3InputHints getInstance(){
        return instance;
    }

    public static class Z3StringHint {

        private Integer inputId;
        private Pair<String, String> hint;

        public Z3StringHint(Integer inputId, Pair<String, String> hint) {
            this.inputId = inputId;
            this.hint = hint;
        }

        public Integer getInputId() {
            return inputId;
        }

        public Pair<String, String> getHint() {
            return hint;
        }
    }

}
