package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicInteger;

public class ThreadID {
  private final AtomicInteger nextID = new AtomicInteger(0);

  private final ThreadLocal<Integer> threadId = ThreadLocal.withInitial(nextID::getAndIncrement);

  public void resetInitialThreadIDTo(int newInitialThreadId) {
    nextID.set(newInitialThreadId);
  }

  public int get() {
    return threadId.get();
  }

  public void set(int index) {
    threadId.set(index);
  }
}
