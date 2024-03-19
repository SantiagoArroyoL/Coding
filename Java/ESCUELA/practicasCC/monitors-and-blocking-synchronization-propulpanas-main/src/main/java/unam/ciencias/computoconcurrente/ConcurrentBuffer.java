package unam.ciencias.computoconcurrente;

public class ConcurrentBuffer<T> implements Buffer<T> {

  private int capacity;
  private volatile int elements;
  private T[] buffer;
  private int head;
  private int tail;

  public ConcurrentBuffer() {
    this(20);
  }

  public ConcurrentBuffer(int capacity) {
    this.capacity = capacity;
    this.buffer = (T[]) new Object[capacity];
    this.elements = 0;
    this.tail = 0;
    this.head = 0;
  }

  @Override
  public int size() {
    return this.capacity;
  }

  @Override
  public synchronized void put(T item) throws InterruptedException {
    while (elements == capacity) {
      wait();
    }
    buffer[tail] = item;
    tail = (tail + 1) % capacity;
    elements++;
    notifyAll();
  }

  @Override
  public synchronized T take() throws InterruptedException {
    while (elements == 0) {
      wait();
    }
    T elem = buffer[head];
    head = (head + 1) % capacity;
    elements--;
    notifyAll();
    return elem;
  }

  @Override
  public int elements() {
    return this.elements;
  }
}
