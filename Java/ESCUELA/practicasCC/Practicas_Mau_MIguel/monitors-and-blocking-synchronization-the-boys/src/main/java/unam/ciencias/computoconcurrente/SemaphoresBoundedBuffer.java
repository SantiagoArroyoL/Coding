package unam.ciencias.computoconcurrente;

import java.util.concurrent.Semaphore;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class SemaphoresBoundedBuffer<T> implements Buffer<T> {
  public static final int DEFAULT_SIZE = 20;

  private final int size;
  private final T[] buffer;
  private int elements;
  private int nextPutIndex;
  private int nextTakeIndex;

  public SemaphoresBoundedBuffer() {
    this(DEFAULT_SIZE);
  }

  public SemaphoresBoundedBuffer(int size) {
    this.size = size;
    this.elements = 0;
    this.nextPutIndex = 0;
    this.nextTakeIndex = 0;
    this.buffer = (T[])new Object[size];
  }

  public int size() {
    return this.size;
  }

  public void put(T item) throws InterruptedException {
    this.buffer[this.nextPutIndex] = item;
    this.nextPutIndex = (this.nextPutIndex + 1) % this.size;
    this.elements++;
  }

  public T take() throws InterruptedException {
    T value;
    this.elements--;
    value = this.buffer[this.nextTakeIndex];
    this.nextTakeIndex = (this.nextTakeIndex + 1) % size;
    return value;
  }

  public int elements() {
    return this.elements;
  }
}
