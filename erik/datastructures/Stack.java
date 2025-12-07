package erik.datastructures;

/**
 * A generic interface for Stack data structures.
 *
 * @param <T> the type of elements in this stack
 */
public interface Stack<T> {

    /**
     * Adds an element to the top of the stack.
     *
     * @param value The element to add.
     */

    //@ requires value != null;
    void push(T value);

    /**
     * Removes the element at the top of this stack and returns it.
     *
     * @return The element popped from the stack.
     * @throws IllegalStateException if the stack is empty.
     */

    //@ ensures \result != null;
    T pop();

    /**
     * Returns the element at the top of this stack without removing it.
     *
     * @return The element at the top of this stack.
     * @throws IllegalStateException if the stack is empty.
     */

    //@ ensures \result != null;
    //@ pure
    T peek();

    /**
     * Tests if this stack is empty.
     *
     * @return {@code true} if this stack is empty; {@code false} otherwise.
     */

    //@ pure
    boolean isEmpty();

    /**
     * Returns the size of this stack.
     *
     * @return The number of elements in this stack.
     */
    
    //@ ensures \result >= 0;
    //@ pure
    int size();

    /**
     * Removes all elements from this stack.
     */
    void makeEmpty();
}
