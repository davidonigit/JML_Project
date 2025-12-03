/**
 * The {CircularBuffer} class implements a generic circular (or ring) buffer.
 * A circular buffer is a fixed-size data structure that operates in a FIFO (First In, First Out) manner.
 * The buffer allows you to overwrite old data when the buffer is full and efficiently use limited memory.
 * When the buffer is full, adding a new item will overwrite the oldest data.
 */

public class CircularBuffer {
    
    private /*@ spec_public @*/ int[] buffer;
    private /*@ spec_public @*/ int readIndex;
    private /*@ spec_public @*/ int writeIndex;
    private /*@ spec_public @*/ int size;
    private /*@ spec_public @*/ int capacity;

    /*@ 
      @ public invariant buffer != null;
      @ public invariant capacity > 0;
      @ public invariant buffer.length == capacity;
      @ public invariant 0 <= size && size <= capacity;
      @ public invariant 0 <= readIndex && readIndex < capacity;
      @ public invariant 0 <= writeIndex && writeIndex < capacity;
      @*/

    /*@
      @ requires cap > 0;
      @ ensures capacity == cap;
      @ ensures size == 0;
      @ ensures readIndex == 0;
      @ ensures writeIndex == 0;
      @ ensures buffer.length == cap;
      @*/
    public CircularBuffer(int cap) {
        this.capacity = cap;
        this.buffer = new int[cap];
        this.readIndex = 0;
        this.writeIndex = 0;
        this.size = 0;
    }

    public /*@ pure @*/ boolean isEmpty() {
        return size == 0;
    }

    public /*@ pure @*/ boolean isFull() {
        return size == capacity;
    }

    /*@
      @ requires !isFull();
      @ requires size < capacity; 
      @ ensures size == \old(size) + 1;
      @ ensures buffer[\old(writeIndex)] == element; 
      @ assignable size, writeIndex, buffer[*];
      @*/
    public void insert(int element) {
        buffer[writeIndex] = element;
        
        int nextIndex = writeIndex + 1;
        if (nextIndex >= capacity) {
            writeIndex = 0;
        } else {
            writeIndex = nextIndex;
        }
        
        size++;
    }

    /*@
      @ requires !isEmpty();
      @ requires size > 0;
      @ ensures size == \old(size) - 1;
      @ ensures \result == buffer[\old(readIndex)];
      @ assignable size, readIndex;
      @*/
    public int remove() {
        int element = buffer[readIndex];
        
        int nextIndex = readIndex + 1;
        if (nextIndex >= capacity) {
            readIndex = 0;
        } else {
            readIndex = nextIndex;
        }

        size--;
        return element;
    }

    public /*@ pure @*/ int getSize() {
        return size;
    }
}