/**
 * The idea of Swap-Sort is to count the number m of smaller values (that are in
 * A) from each element of an array A(1...n) and then swap the element with the
 * element in A(m+1). This ensures that the exchanged element is already in the
 * correct, i.e. final, position. The disadvantage of this algorithm is that
 * each element may only occur once, otherwise there is no termination.
 */
public class SwapSort {

    /*@ public normal_behavior
      @   requires array != null;
      @   requires (\forall int i, j; 0 <= i && i < j && j < array.length; array[i] != array[j]);
      @   assignable array[*];
      @*/
    public void sort(int[] array) {
        int index = 0;

        if (array.length == 0) return;

        //@ loop_invariant 0 <= index < array.length;
        while (index < array.length - 1) {
            int amountSmallerElements = getSmallerElementCount(array, index);

            if (amountSmallerElements > 0) {
                int target = index + amountSmallerElements;
                //@ assert target < array.length;

                int temp = array[index];
                array[index] = array[target];
                array[target] = temp;
            } else {
                index++;
            }
        }
    }

    /*@ private normal_behavior
      @   requires array != null;
      @   requires 0 <= index < array.length;
      @   ensures 0 <= \result <= (array.length - 1 - index);
      @*/
    private /*@ pure helper @*/ int getSmallerElementCount(int[] array, int index) {
        int counter = 0;
        
        /*@ loop_invariant index + 1 <= i <= array.length;
          @ loop_invariant 0 <= counter <= (i - (index + 1));
          @ decreases array.length - i;
          @*/
        for (int i = index + 1; i < array.length; i++) {
            if (array[i] < array[index]) {
                counter++;
            }
        }
        return counter;
    }
}