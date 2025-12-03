/**
 * Linear search is the easiest search algorithm It works with sorted and
 * unsorted arrays (an binary search works only with sorted array) This
 * algorithm just compares all elements of an array to find a value
 */
public class LinearSearch {

    /*@ public normal_behavior
      @   requires array != null;
      @   ensures \result != -1 ==> (0 <= \result && \result < array.length && array[\result] == value);
      @   ensures \result == -1 ==> (\forall int k; 0 <= k && k < array.length; array[k] != value);
      @*/
    public /*@ pure @*/ int find(int[] array, int value) {
        
        /*@ loop_invariant 0 <= i && i <= array.length;
          @ loop_invariant (\forall int k; 0 <= k && k < i; array[k] != value);
          @ decreases array.length - i;
          @*/
        for (int i = 0; i < array.length; i++) {
            if (array[i] == value) {
                return i;
            }
        }
        return -1;
    }
}