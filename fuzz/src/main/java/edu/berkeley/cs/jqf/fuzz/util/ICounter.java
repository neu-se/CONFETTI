package edu.berkeley.cs.jqf.fuzz.util;

import java.util.Collection;

public interface ICounter {
    /**
     * Returns the size of this counter.
     *
     * @return the size of this counter
     */
    int size();

    /**
     * Clears the counter by setting all values to zero.
     */
    void clear();

    /**
     * Increments the count at the given key.
     *
     * <p>Note that the key is hashed and therefore the count
     * to increment may be shared with another key that hashes
     * to the same value. </p>
     *
     * @param key the key whose count to increment
     * @return the new value after incrementing the count
     */
    int increment(int key);

    /**
     *
     * Increments the count at the given key by a given delta.
     *
     * <p>Note that the key is hashed and therefore the count
     * to increment may be shared with another key that hashes
     * to the same value. </p>
     *
     * @param key the key whose count to increment
     * @param delta the amount to increment by
     * @return the new value after incrementing the count
     */
    int increment(int key, int delta);

    /**
     * Returns the number of indices with non-zero counts.
     *
     * @return the number of indices with non-zero counts
     */
    int getNonZeroSize();

    /**
     * Returns a set of indices at which the count is non-zero.
     *
     * <p>Note that indices are different from keys, in that
     * multiple keys can map to the same index due to hash
     * collisions.</p>
     *
     * @return a set of indices at which the count is non-zero
     */
    Collection<Integer> getNonZeroIndices();

    /**
     * Returns a set of non-zero count values in this counter.
     *
     * @return a set of non-zero count values in this counter.
     */
    Collection<Integer> getNonZeroValues();

    /**
     * Retreives a value for a given key.
     *
     * <p>The key is first hashed to retreive a value from
     * the counter, and hence the result is modulo collisions.</p>
     *
     * @param key the key to query
     * @return the count for the index corresponding to this key
     */
    int get(int key);

    int getAtIndex(int idx);

    void setAtIndex(int idx, int value);
}
