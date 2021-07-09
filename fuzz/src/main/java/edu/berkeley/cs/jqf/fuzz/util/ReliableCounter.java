package edu.berkeley.cs.jqf.fuzz.util;


import org.eclipse.collections.api.iterator.MutableIntIterator;
import org.eclipse.collections.api.list.primitive.IntList;
import org.eclipse.collections.api.map.primitive.MutableIntIntMap;
import org.eclipse.collections.api.tuple.primitive.IntIntPair;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.primitive.IntIntHashMap;

import java.util.Iterator;

public class ReliableCounter {

    public MutableIntIntMap map = new IntIntHashMap(1 << 8);
    public synchronized int size() {
        return map.size();
    }

    public synchronized void clear() {
        map.clear();
    }

    public synchronized int increment(int key) {
        int existing = map.get(key);
        int newVal = existing + 1;
        map.put(key, newVal);
        return newVal;
    }

    public synchronized int increment(int key, int delta) {
        int existing = map.get(key);
        int newVal = existing + delta;
        map.put(key, newVal);
        return newVal;
    }

    public synchronized int getNonZeroSize() {
        int size = 0;
        MutableIntIterator iter = map.values().intIterator();
        while(iter.hasNext()){
            if(iter.next() != 0){
                size++;
            }
        }
        return size;
    }

    public synchronized IntList getNonZeroKeys() {
        IntArrayList indices = new IntArrayList(map.size()/2);
        Iterator<IntIntPair> iter = map.keyValuesView().iterator();
        while(iter.hasNext()){
            IntIntPair each = iter.next();
            if(each.getTwo() != 0){
                indices.add(each.getOne());
            }
        }
        return indices;
    }

    public synchronized IntList getNonZeroValues() {
        IntArrayList values = new IntArrayList(map.size() / 2);
        Iterator<IntIntPair> iter = map.keyValuesView().iterator();
        while (iter.hasNext()) {
            IntIntPair each = iter.next();
            if (each.getTwo() != 0) {
                values.add(each.getTwo());
            }
        }
        return values;

    }

    public synchronized int get(int key) {
        return map.get(key);
    }

    public void copyFrom(ReliableCounter counter) {
        this.map = new IntIntHashMap(counter.map);
    }
}
