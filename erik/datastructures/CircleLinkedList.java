package com.thealgorithms.datastructures.lists;

import java.util.Optional;

/**
 * This class is a circular singly linked list implementation. In a circular linked list,
 * the last node points back to the first node, creating a circular chain.
 *
 * <p>This implementation includes basic operations such as appending elements
 * to the end, removing elements from a specified position, and converting
 * the list to a string representation.
 *
 * @param <E> the type of elements held in this list
 */
@SuppressWarnings("rawtypes")
public class CircleLinkedList<E> {

    //@ public invariant 0 <= size && size <= Integer.MAX_VALUE;

    /**
     * A static nested class representing a node in the circular linked list.
     *
     * @param <E> the type of element stored in the node
     */
    static final class Node<E> {

        /*@ spec_public @*/
        Node<E> next;

        /*@ spec_public @*/
        Optional<E> value;

        /*@ pure @*/
        private Node() {
            this.next = this;
            this.value = Optional.empty();
        }

        /*@ pure @*/
        private Node(Optional<E> value, Node<E> next) {
            this.value = value;
            this.next = next;
        }
    }

    /*@ spec_public @*/
    private int size;

    /*@
      @ spec_public 
    @*/
    Node<E> head;

    /*@ spec_public @*/
    private Node<E> tail;

    /**
     * Initializes a new circular linked list. A dummy head node is used for simplicity,
     * pointing initially to itself to ensure the list is never empty.
     */

    /*@ pure @*/
    public CircleLinkedList() {
        head = new Node<>();
        tail = head;
        size = 0;
    }

    /**
     * Returns the current size of the list.
     *
     * @return the number of elements in the list
     */

    /*@ 
      @ ensures \result == size; 
      @  pure 
      @*/
    public int getSize() {
        return size;
    }

    /**
     * Appends a new element to the end of the list. Throws a NullPointerException if
     * a null value is provided.
     *
     * @param value the value to append to the list
     * @throws NullPointerException if the value is null
     */

    /*@ 
      @ requires size < Integer.MAX_VALUE;
      @ ensures size == \old(size) + 1;
      @*/
    public void append(Optional<E> value) {
        if (value == null) {
            throw new NullPointerException("Cannot add null element to the list");
        }
        if (tail == null) {
            tail = new Node<>(value, head);
            head.next = tail;
        } else {
            tail.next = new Node<>(value, head);
            tail = tail.next;
        }
        size++;
    }

    /**
     * Removes and returns the element at the specified position in the list.
     * Throws an IndexOutOfBoundsException if the position is invalid.
     *
     * @param pos the position of the element to remove
     * @return the value of the removed element
     * @throws IndexOutOfBoundsException if the position is out of range
     */

    /*@
      @ requires 0 <= pos && pos < size;
      @*/
    public Optional<E> remove(int pos) {
        if (pos >= size || pos < 0) {
            throw new IndexOutOfBoundsException("Position out of bounds");
        }

        Node<E> before = head;

        /*@
          @ loop_invariant 1 <= i && i <= pos + 1;
          @ decreases pos + 1 - i;
          @*/
        for (int i = 1; i <= pos; i++) {
            before = before.next;
        }
        Node<E> destroy = before.next;
        Optional<E> saved = destroy.value;
        before.next = destroy.next;

        if (destroy == tail) {
            tail = before;
        }

        size--;
        return saved;
    }
}
