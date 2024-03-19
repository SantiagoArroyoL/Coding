package unam.ciencias.computoconcurrente;


public class SemaphoresBoundedBuffer<T> implements Buffer<T> {
  public static final int DEFAULT_SIZE = 20;

  private final int size;
  private final T[] buffer;
  private int elements;

  public SemaphoresBoundedBuffer() {
    this(DEFAULT_SIZE);
  }

  public SemaphoresBoundedBuffer(int size) {
    this.size = size;
    this.buffer = (T[]) new Object[this.size];
    this.elements = 0;
  }

  public int size() {
    return this.size;
  }

  public void put(T item) throws InterruptedException {}

  public T take() throws InterruptedException {
    return null;
  }

  public int elements() {
    return 0;
  }
}
