package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicInteger;

public class ThreadID {
  private static final AtomicInteger nextID = new AtomicInteger(0);

  private static final ThreadLocal<Integer> threadId =
      ThreadLocal.withInitial(nextID::getAndIncrement);

  public static void resetInitialThreadIDTo(int newInitialThreadId) {
    nextID.set(newInitialThreadId);
  }

  public static int get() {
    return threadId.get();
  }

  public static void set(int index) {
    threadId.set(index);
  }
}
