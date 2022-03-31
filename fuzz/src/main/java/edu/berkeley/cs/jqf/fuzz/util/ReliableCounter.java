package edu.berkeley.cs.jqf.fuzz.util;


import edu.columbia.cs.psl.phosphor.struct.IntSinglyLinkedList;
import org.eclipse.collections.api.iterator.IntIterator;
import org.eclipse.collections.api.list.primitive.IntList;
import org.eclipse.collections.api.map.primitive.MutableIntIntMap;
import org.eclipse.collections.api.tuple.primitive.IntIntPair;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.primitive.IntIntHashMap;

import java.util.Iterator;

public class ReliableCounter {

    public IntSinglyLinkedList nonZeroKeys = new IntSinglyLinkedList();
    public MutableIntIntMap map = new IntIntHashMap(1 << 8);
    public synchronized int size() {
        return map.size();
    }

    public synchronized void clear() {
        map.clear();
        nonZeroKeys.clear();
    }

    public synchronized int increment(int key) {
        int newVal = map.addToValue(key, 1);
        if(newVal == 1){
            nonZeroKeys.addFirst(key);
        }
        return newVal;
    }

    public synchronized int increment(int key, int delta) {
        int newVal = map.addToValue(key, delta);
        if(newVal == delta){
            nonZeroKeys.addFirst(key);
        }
        return newVal;
    }

    public synchronized int getNonZeroSize() {
        return nonZeroKeys.size();
    }

    public synchronized IntSinglyLinkedList getNonZeroKeys() {
        return nonZeroKeys;
    }

    public synchronized IntList getNonZeroValues() {
        IntArrayList values = new IntArrayList(map.size() / 2);
        IntIterator iter = map.values().intIterator();
        while (iter.hasNext()) {
            int val = iter.next();
            if (val != 0) {
                values.add(val);
            }
        }
        return values;

    }

    public synchronized int get(int key) {
        return map.get(key);
    }

    public void copyFrom(ReliableCounter counter) {
        this.map = new IntIntHashMap(counter.map);
        this.nonZeroKeys = new IntSinglyLinkedList();
        IntSinglyLinkedList.IntListIterator iter = counter.nonZeroKeys.iterator();
        while(iter.hasNext()){
            this.nonZeroKeys.addFirst(iter.next());
        }
    }
}
