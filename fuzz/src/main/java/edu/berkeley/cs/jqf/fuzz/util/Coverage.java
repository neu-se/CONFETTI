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
package edu.berkeley.cs.jqf.fuzz.util;

import edu.berkeley.cs.jqf.instrument.tracing.events.BranchEvent;
import edu.berkeley.cs.jqf.instrument.tracing.events.CallEvent;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEvent;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEventVisitor;
import edu.columbia.cs.psl.phosphor.struct.IntSinglyLinkedList;
import janala.instrument.CoverageListener;
import org.eclipse.collections.api.IntIterable;
import org.eclipse.collections.api.iterator.IntIterator;
import org.eclipse.collections.api.list.primitive.IntList;
import org.eclipse.collections.api.tuple.primitive.IntIntPair;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;

import java.util.Iterator;

/**
 * Utility class to collect branch and function coverage
 *
 * @author Rohan Padhye
 */
public class Coverage implements TraceEventVisitor, CoverageListener {

    /** The size of the coverage map. */
    private final int COVERAGE_MAP_SIZE = (1 << 16) - 1; // Minus one to reduce collisions

    /** The coverage counts for each edge. */
    //private final Counter counter = new NonZeroCachingCounter(COVERAGE_MAP_SIZE);
    private final ReliableCounter counter = new ReliableCounter();

    private boolean lock = false;
    /** Creates a new coverage map. */
    public Coverage() {

    }

    /**
     * Creates a copy of an existing coverage map.
     *
     * @param that the coverage map to copy
     */
    public Coverage(Coverage that) {
        //for (int idx = 0; idx < COVERAGE_MAP_SIZE; idx++) {
        //    this.counter.setAtIndex(idx, that.counter.getAtIndex(idx));
        //}
        this.counter.copyFrom(that.counter);
    }

    /**
     * Returns the size of the coverage map.
     *
     * @return the size of the coverage map
     */
    public int size() {
        return COVERAGE_MAP_SIZE;
    }

    /**
     * Updates coverage information based on emitted event.
     *
     * <p>This method updates its internal counters for branch and
     * call events.</p>
     *
     * @param e the event to be processed
     */
    public void handleEvent(TraceEvent e) {
        e.applyVisitor(this);
    }

    @Override
    public void visitBranchEvent(BranchEvent b) {
        if(!lock) {
            //This might still not be quite right - is it possible to overflow here and have a collision?
            //Also note switch statements will have many arms...
            counter.increment((b.getIid() << 2) + b.getArm());
        }
    }

    @Override
    public void visitCallEvent(CallEvent e) {
        if(!lock) {
            counter.increment((e.getIid() << 2) + 3);
        }
    }

    /**
     * Returns the number of edges covered.
     *
     * @return the number of edges with non-zero counts
     */
    public int getNonZeroCount() {
        return counter.getNonZeroSize();
    }

    /**
     * Returns a collection of branches that are covered.
     *
     * @return a collection of keys that are covered
     */
    public IntSinglyLinkedList getCovered() {
        return counter.getNonZeroKeys();
    }


    public IntList computeNewCoverage(Coverage baseline) {
        IntArrayList newCoverage = new IntArrayList();

        IntSinglyLinkedList baseNonZero = this.counter.getNonZeroKeys();
        IntSinglyLinkedList.IntListIterator iter = baseNonZero.iterator();
        while (iter.hasNext()) {
            int idx = iter.nextInt();
            if (baseline.counter.get(idx) == 0) {
                newCoverage.add(idx);
            }
        }
        return newCoverage;

    }



    /**
     * Clears the coverage map.
     */
    public void clear() {
        this.counter.clear();
    }

    public void lock() {
        lock = true;
    }

    public void unlock() {
        lock = false;
    }

    private static int[] HOB_CACHE = new int[1024];

    /** Computes the highest order bit */
    private static int computeHob(int num)
    {
        if (num == 0)
            return 0;

        int ret = 1;

        while ((num >>= 1) != 0)
            ret <<= 1;

        return ret;
    }

    /** Populates the HOB cache. */
    static {
        for (int i = 0; i < HOB_CACHE.length; i++) {
            HOB_CACHE[i] = computeHob(i);
        }
    }

    /** Returns the highest order bit (perhaps using the cache) */
    private static int hob(int num) {
        if (num < HOB_CACHE.length) {
            return HOB_CACHE[num];
        } else {
            return computeHob(num);
        }
    }


    /**
     * Updates this coverage with bits from the parameter.
     *
     * @param that the run coverage whose bits to OR
     *
     * @return <tt>true</tt> iff <tt>that</tt> is not a subset
     *         of <tt>this</tt>, causing <tt>this</tt> to change.
     */
    public boolean updateBits(Coverage that) {
        boolean changed = false;
        //for (int idx = 0; idx < COVERAGE_MAP_SIZE; idx++) {
        //    int before = this.counter.getAtIndex(idx);
        //    int after = before | hob(that.counter.getAtIndex(idx));
        //    if (after != before) {
        //        this.counter.setAtIndex(idx, after);
        //        changed = true;
        //    }
        //}
        synchronized (this.counter){
            synchronized (that.counter){
                Iterator<IntIntPair> thatIter = that.counter.map.keyValuesView().iterator();

                while(thatIter.hasNext()){
                    IntIntPair coverageEntry = thatIter.next();
                    int before = this.counter.map.get(coverageEntry.getOne());
                    int after = before | hob(coverageEntry.getTwo());
                    if(after != before){
                        this.counter.map.put(coverageEntry.getOne(), after);
                        changed = true;
                    }
                    if(before == 0){
                        this.counter.nonZeroKeys.addFirst(coverageEntry.getOne());
                    }
                }
            }
        }
        return changed;
    }

    private int cachedSize = -1;

    public CoverageComparisonResult compareCoverage(Coverage that){
        synchronized (this.counter){
            synchronized (that.counter){
                Iterator<IntIntPair> thisIter = this.counter.map.keyValuesView().iterator();
                if(cachedSize == -1)
                    this.cachedSize = this.counter.map.size();
                if(that.counter.map.size() < cachedSize)
                    return CoverageComparisonResult.THAT_DOES_NOT_COVER_ALL_OF_THIS;

                boolean coversAllOfThis = true;
                boolean coversAllOfThisSameOrGreaterHits = true;
                while(thisIter.hasNext()){
                    IntIntPair coverageEntry = thisIter.next();
                    if(coverageEntry.getTwo() == 0)
                        continue;
                    int thatStatus = that.counter.map.get(coverageEntry.getOne());
                    if(thatStatus == 0){
                        coversAllOfThis = false;
                        coversAllOfThisSameOrGreaterHits = false;
                        break;
                    }
                    else if(thatStatus < coverageEntry.getTwo()) {
                        coversAllOfThisSameOrGreaterHits = false;
                    }
                }
                if(coversAllOfThisSameOrGreaterHits)
                    return CoverageComparisonResult.THAT_COVERS_ALL_OF_THIS_SAME_OR_GREATER_HITS;
                if(coversAllOfThis)
                    return CoverageComparisonResult.THAT_COVERS_ALL_OF_THIS;
                return CoverageComparisonResult.THAT_DOES_NOT_COVER_ALL_OF_THIS;
            }
        }
    }
    public static enum CoverageComparisonResult{
        THAT_COVERS_ALL_OF_THIS,
        THAT_COVERS_ALL_OF_THIS_SAME_OR_GREATER_HITS,
        THAT_DOES_NOT_COVER_ALL_OF_THIS
    }

    @Override
    public void logCoverage(int iid, int arm) {
        counter.increment(iid  + arm);
    }

    public ReliableCounter getCounter() {
        return counter;
    }
}
