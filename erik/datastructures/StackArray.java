package com.thealgorithms.datastructures.stacks;

/**
 * Implements a generic stack using an array.
 *
 * <p>This stack automatically resizes when necessary, growing to accommodate additional elements and
 * shrinking to conserve memory when its size significantly decreases.
 *
 * <p>Elements are pushed and popped in LIFO (last-in, first-out) order, where the last element added
 * is the first to be removed.
 *
 * @param <T> the type of elements in this stack
 */
public class StackArray<T> {

    //@ public invariant 0 <= maxSize && maxSize <= Integer.MAX_VALUE;
    //@ public invariant stackArray.length == maxSize;
    //@ public invariant -1 <= top && top < maxSize;
    //@ public invariant \typeof(stackArray) == \type(Object[]);
    //@ public invariant (\forall int k; 0 <= k && k <= top; stackArray[k] != null);

    /*@ spec_public @*/
    private static final int DEFAULT_CAPACITY = 10;
    /*@ spec_public @*/
    private int maxSize;
    /*@ spec_public @*/
    private T[] stackArray;
    /*@ spec_public @*/
    private int top;

    /**
     * Creates a stack with a default capacity.
     */

    /*@ public normal_behavior
      @ requires 0 <= DEFAULT_CAPACITY && DEFAULT_CAPACITY <= Integer.MAX_VALUE;
      @*/
    @SuppressWarnings("unchecked")
    public StackArray() {
        this(DEFAULT_CAPACITY);
    }

    /**
     * Creates a stack with a specified initial capacity.
     *
     * @param size the initial capacity of the stack, must be greater than 0
     * @throws IllegalArgumentException if size is less than or equal to 0
     */

    /*@ public normal_behavior
      @     requires size > 0;
      @     ensures stackArray.length == size;
      @     ensures top == -1;
      @ also
      @ public exceptional_behavior
      @     requires size <= 0;
      @     signals (IllegalArgumentException e) true;
      @*/
    @SuppressWarnings("unchecked")
    public StackArray(int size) {
        if (size <= 0) {
            throw new IllegalArgumentException("Stack size must be greater than 0");
        }
        this.maxSize = size;
        this.stackArray = (T[]) new Object[size];
        this.top = -1;
    }

    /**
     * Pushes an element onto the top of the stack. Resizes the stack if it is full.
     *
     * @param value the element to push
     */
    /*@ public normal_behavior
      @   requires !isFull();
      @   requires value != null;
      @   requires \typeof(value) == \elemtype(stackArray);
      @   ensures stackArray[top] == value;
      @   ensures top == \old(top) + 1;
    @*/
    public void push(T value) {
        if (isFull()) {
            resize(maxSize * 2);
        }
        stackArray[++top] = value;
    }

    /**
     * Removes and returns the element from the top of the stack. Shrinks the stack if
     * its size is below a quarter of its capacity, but not below the default capacity.
     *
     * @return the element removed from the top of the stack
     * @throws IllegalStateException if the stack is empty
     */

    
    /*@ public normal_behavior
      @   requires !isEmpty();
      @   ensures \result == \old(stackArray[top]);
      @ also
      @ public exceptional_behavior
      @   requires isEmpty();
      @   signals (IllegalStateException e) true;
    @*/
    public T pop() {
        if (isEmpty()) {
            throw new IllegalStateException("Stack is empty, cannot pop element");
        }
        T value = stackArray[top--];
        if (top + 1 < maxSize / 4 && maxSize > DEFAULT_CAPACITY) {
            resize(maxSize / 2);
        }
        return value;
    }

    /**
     * Returns the element at the top of the stack without removing it.
     *
     * @return the top element of the stack
     * @throws IllegalStateException if the stack is empty
     */

    /*@ public normal_behavior
      @   requires !isEmpty();
      @   ensures \result == stackArray[top];
      @ also
      @ public exceptional_behavior
      @   requires isEmpty();
      @   signals (IllegalStateException e) true;
    @*/
    public T peek() {
        if (isEmpty()) {
            throw new IllegalStateException("Stack is empty, cannot peek element");
        }
        return stackArray[top];
    }

    /**
     * Resizes the internal array to a new capacity.
     *
     * @param newSize the new size of the stack array
     */

    /*@ private normal_behavior
      @   requires 0 <= newSize && newSize >= top + 1;
      @   requires \typeof(stackArray) == \type(Object[]);
      @   assignable stackArray, maxSize;
    @*/
    private void resize(int newSize) {
        @SuppressWarnings("unchecked") T[] newArray = (T[]) new Object[newSize];

        /*@ loop_invariant 0 <= i && i <= top + 1;
          @ loop_invariant (\forall int k; 0 <= k && k < i; newArray[k] == stackArray[k]); 
          @ decreases (top + 1) - i;
          @*/
        for (int i = 0; i <= top; i++) {
            newArray[i] = stackArray[i];
        }        
        stackArray = newArray;
        maxSize = newSize;
    }

    /**
     * Checks if the stack is full.
     *
     * @return true if the stack is full, false otherwise
     */

    /*@ public normal_behavior
      @   ensures \result == (top + 1 == maxSize);
      @ pure
    @*/
    public boolean isFull() {
        return top + 1 == maxSize;
    }

    /**
     * Checks if the stack is empty.
     *
     * @return true if the stack is empty, false otherwise
     */

    /*@ public normal_behavior
      @   ensures \result == (top == -1);
      @ pure
    @*/
    public boolean isEmpty() {
        return top == -1;
    }

    /**
     * Empties the stack, marking it as empty without deleting elements. Elements are
     * overwritten on subsequent pushes.
     */

    /*@ public normal_behavior
      @   ensures top == -1;
    @*/
    public void makeEmpty() {
        top = -1;
    }

    /**
     * Returns the number of elements currently in the stack.
     *
     * @return the size of the stack
     */

    /*@ public normal_behavior
      @   ensures \result == top + 1;
      @ pure
    @*/
    public int size() {
        return top + 1;
    }
}
