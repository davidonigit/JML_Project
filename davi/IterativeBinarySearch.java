/**
 * Binary search is one of the most popular algorithms This class represents
 * iterative version {@link BinarySearch} Iterative binary search is likely to
 * have lower constant factors because it doesn't involve the overhead of
 * manipulating the call stack. But in java the recursive version can be
 * optimized by the compiler to this version.
 */
public class IterativeBinarySearch {

    /*@ public normal_behavior
      @   requires array != null;
      @   requires (\forall int i, j; 0 <= i && i < j && j < array.length; array[i] <= array[j]);
      @   ensures \result != -1 ==> (0 <= \result && \result < array.length && array[\result] == key);
      @   ensures \result == -1 ==> (\forall int i; 0 <= i && i < array.length; array[i] != key);
      @*/
    public /*@ pure @*/ int find(int[] array, int key) {
        int l = 0;
        int r = array.length - 1;
        int k;

        /*@ loop_invariant 0 <= l && r < array.length;
          @ loop_invariant (\forall int i; 0 <= i && i < l; array[i] < key);
          @ loop_invariant (\forall int i; r < i && i < array.length; array[i] > key);
          @ decreases r - l + 1;
          @*/
        while (l <= r) {
            k = l + (r - l) / 2;

            if (array[k] == key) {
                return k;
            } else if (array[k] > key) {
                r = --k;
            } else {
                l = ++k;
            }
        }
        return -1;
    }
}