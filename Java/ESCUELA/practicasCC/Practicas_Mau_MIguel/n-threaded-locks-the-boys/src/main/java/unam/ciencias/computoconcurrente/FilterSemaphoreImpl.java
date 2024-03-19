package unam.ciencias.computoconcurrente;

public class FilterSemaphoreImpl extends Semaphore {

  private final int capacity;
  private final int threads;

  public FilterSemaphoreImpl(int threads, int permits) {
    this.threads = threads;
    this.capacity = permits;
  }

  @Override
  public void down() {}

  @Override
  public void up() {}
}
