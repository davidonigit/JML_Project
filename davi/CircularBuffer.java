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
      @ public initially size == 0;
      @ public initially readIndex == 0;
      @ public initially writeIndex == 0;
      @ public invariant buffer != null;
      @ public invariant capacity > 0;
      @ public invariant buffer.length == capacity;
      @ public invariant 0 <= size <= capacity;
      @ public invariant 0 <= readIndex < capacity;
      @ public invariant 0 <= writeIndex < capacity;
      @*/

    /*@
      @ requires cap > 0 && cap < Integer.MAX_VALUE;
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
      @ public exceptional_behavior
      @   requires element == 0;
      @   assignable \nothing;
      @   signals_only IllegalArgumentException;
      @ 
      @ also
      @
      @ public normal_behavior    
      @   requires size < capacity;
      @   requires element != 0;
      @   assignable size, writeIndex, buffer[*];
      @   ensures size == \old(size) + 1;
      @   ensures buffer[\old(writeIndex)] == element;
      @   ensures writeIndex == (\old(writeIndex) + 1) % capacity;
      @   ensures readIndex == \old(readIndex);
      @
      @ also
      @
      @ public normal_behavior  
      @   requires size == capacity;
      @   requires element != 0;
      @   assignable readIndex, writeIndex, buffer[*];
      @   ensures size == capacity;
      @   ensures buffer[\old(writeIndex)] == element;
      @   ensures writeIndex == (\old(writeIndex) + 1) % capacity;
      @   ensures readIndex == (\old(readIndex) + 1) % capacity;
      @*/
    public void put(int element) {    
        if (element == 0){
            throw new IllegalArgumentException("Elemento 0 nao e permitido");
        }
        if (size < capacity) {
            buffer[writeIndex] = element;

            writeIndex = (writeIndex + 1) % capacity;
            
            size++;
        } else {
            buffer[writeIndex] = element;
            
            writeIndex = (writeIndex + 1) % capacity;
            readIndex = (readIndex + 1) % capacity;
        }
    }

    /*@
      @ public normal_behavior
      @   requires size == 0;
      @   assignable \nothing;
      @   ensures \result == 0;
      @
      @ also
      @
      @ public normal_behavior
      @   requires size > 0;
      @   assignable size, readIndex, buffer[*];
      @   ensures size == \old(size) - 1;
      @   ensures \result == \old(buffer[readIndex]);
      @   ensures buffer[\old(readIndex)] == 0;
      @   ensures readIndex == (\old(readIndex) + 1) % capacity;
      @*/
    public int get() {
        if (size == 0) {
            return 0;
        } else {
            int element = buffer[readIndex];
            buffer[readIndex] = 0;
            
            readIndex = (readIndex + 1) % capacity;
            
            size--;
            return element;
        }
    }

    public /*@ pure @*/ int getSize() {
        return size;
    }
}