package com.thealgorithms.datastructures.queues;

/**
 * This class implements a Queue data structure using an array.
 * A queue is a first-in-first-out (FIFO) data structure where elements are
 * added to the rear and removed from the front.
 *
 * Note: This implementation is not thread-safe.
 */
public final class Queue<T> {

    //@ public invariant 0 <= front && front < maxSize;
    //@ public invariant -1 <= rear && rear < maxSize;
    //@ public invariant 0 <= nItems && nItems <= maxSize;
    //@ public invariant queueArray.length <= maxSize;

    /*@ spec_public @*/
    private static final int DEFAULT_CAPACITY = 10;
    /*@ spec_public @*/
    private final int maxSize;
    /*@ spec_public @*/
    private final Object[] queueArray;
    /*@ spec_public @*/
    private int front;
    /*@ spec_public @*/
    private int rear;
    /*@ spec_public @*/
    private int nItems;


    /**
     * Initializes a queue with a default capacity.
     */
    /*@ private normal_behavior
      @ ensures maxSize == DEFAULT_CAPACITY;
      @ ensures queueArray.length == DEFAULT_CAPACITY;
      @ ensures front == 0 && rear == -1 && nItems == 0;
      @*/
    public Queue() {
        this(DEFAULT_CAPACITY);
    }

    /**
     * Constructor to initialize a queue with a specified capacity.
     *
     * @param capacity The initial size of the queue.
     * @throws IllegalArgumentException if the capacity is less than or equal to zero.
     */

    /*@ private normal_behavior
      @     requires capacity > 0;
      @     ensures maxSize == capacity;
      @     ensures queueArray.length == capacity;
      @     ensures front == 0 && rear == -1 && nItems == 0;
      @ also
      @ private exceptional_behavior
      @     requires capacity <= 0;
      @     signals (IllegalArgumentException e) true;
    @*/
    public Queue(int capacity) {
        if (capacity <= 0) {
            throw new IllegalArgumentException("Queue capacity must be greater than 0");
        }
        this.maxSize = capacity;
        this.queueArray = new Object[capacity];
        this.front = 0;
        this.rear = -1;
        this.nItems = 0;
    }

    /**
     * Inserts an element at the rear of the queue.
     *
     * @param element Element to be added.
     * @return True if the element was added successfully, false if the queue is full.
     */

    /*@ public normal_behavior 
      @   requires queueArray != null && element != null;
      @   requires !isFull();
      @   requires \typeof(element) == \elemtype(queueArray);
      @   requires maxSize <= queueArray.length;
      @   requires 0 <= rear && rear < maxSize;
      @   ensures nItems == \old(nItems) + 1;
      @   ensures rear == (\old(rear) + 1) % maxSize;
      @   ensures front == \old(front);
      @   ensures \result == true;
      @ also
      @ public normal_behavior
      @   requires isFull();
      @   ensures \result == false; 
      @*/
    public boolean insert(T element) {
        if (isFull()) {
            return false;
        }
        rear = (rear + 1) % maxSize;
        queueArray[rear] = element;
        nItems++;
        return true;
    }

    /**
     * Removes and returns the element from the front of the queue.
     *
     * @return The element removed from the front of the queue.
     * @throws IllegalStateException if the queue is empty.
     */

    /*@ public normal_behavior
      @   requires !isEmpty();
      @   requires maxSize <= queueArray.length;
      @   requires 0 <= rear && rear < maxSize;
      @   ensures nItems == \old(nItems) - 1;
      @   ensures front == (\old(front) + 1) % maxSize;
      @   ensures rear == \old(rear);
      @ also
      @ public exceptional_behavior
      @   requires isEmpty();
      @   signals (IllegalStateException e) true;
    @*/
    @SuppressWarnings("unchecked")
    public T remove() {
        if (isEmpty()) {
            throw new IllegalStateException("Queue is empty, cannot remove element");
        }
        T removedElement = (T) queueArray[front];
        // queueArray[front] = null; // Optional: Clear the reference for garbage collection
        front = (front + 1) % maxSize;
        nItems--;
        return removedElement;
    }

    /**
     * Checks the element at the front of the queue without removing it.
     *
     * @return Element at the front of the queue.
     * @throws IllegalStateException if the queue is empty.
     */

    /*@
      @ public normal_behavior
      @   requires !isEmpty() && queueArray != null;
      @   requires maxSize <= queueArray.length;
      @   requires 0 <= rear && rear < maxSize;
      @   ensures \result == queueArray[front];
      @ also
      @ public exceptional_behavior
      @   requires isEmpty();
      @   signals (IllegalStateException e) true;
      @ pure
    @*/
    @SuppressWarnings("unchecked")
    public T peekFront() {
        if (isEmpty()) {
            throw new IllegalStateException("Queue is empty, cannot peek front");
        }
        return (T) queueArray[front];
    }

    /**
     * Checks the element at the rear of the queue without removing it.
     *
     * @return Element at the rear of the queue.
     * @throws IllegalStateException if the queue is empty.
     */

    /*@ public normal_behavior
      @   requires !isEmpty() && queueArray != null;
      @   requires maxSize <= queueArray.length;
      @   requires 0 <= rear && rear < maxSize;
      @   ensures \result == queueArray[rear];
      @ also
      @ public exceptional_behavior
      @   requires isEmpty();
      @   signals (IllegalStateException e) true;
      @ pure
    @*/
    @SuppressWarnings("unchecked")
    public T peekRear() {
        if (isEmpty()) {
            throw new IllegalStateException("Queue is empty, cannot peek rear");
        }
        return (T) queueArray[rear];
    }

    /**
     * Returns true if the queue is empty.
     *
     * @return True if the queue is empty.
     */

    /*@
      @ public normal_behavior
      @ ensures \result == (nItems == 0);
      @ pure
    @*/
    public boolean isEmpty() {
        return nItems == 0;
    }

    /**
     * Returns true if the queue is full.
     *
     * @return True if the queue is full.
     */

    /*@ public normal_behavior
      @ ensures \result == (nItems == maxSize);
      @ pure
    @*/
    public boolean isFull() {
        return nItems == maxSize;
    }

    /**
     * Returns the number of elements currently in the queue.
     *
     * @return Number of elements in the queue.
     */

    /*@ public normal_behavior
      @ ensures \result == nItems;
      @ pure
    @*/
    public int getSize() {
        return nItems;
    }
}
