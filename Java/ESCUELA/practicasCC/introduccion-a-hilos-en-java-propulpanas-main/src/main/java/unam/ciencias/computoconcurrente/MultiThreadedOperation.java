package unam.ciencias.computoconcurrente;

import java.util.List;

public class MultiThreadedOperation {
  protected final int threads;

  public MultiThreadedOperation() {
    this.threads = 1;
  }

  public MultiThreadedOperation(int threads) {
    this.threads = threads;
  }

  protected void runAndWaitForThreads(List<Thread> threads) throws InterruptedException {
    threads.forEach(Thread::start);
    for (Thread t : threads) {
      t.join();
    }
  }
}
