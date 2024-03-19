package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicIntegerArray;

public class FilterLock implements Lock {

  private int threads;
  private AtomicIntegerArray level;
  private AtomicIntegerArray victim;

  public FilterLock(int threads) {
    this.threads = threads;
    this.level = new AtomicIntegerArray(threads);
    this.victim = new AtomicIntegerArray(threads);
  }

  @Override
  public void lock() {
    int threadId = ThreadID.get();

    // Establecer el nivel actual del hilo en threads - 1
    for (int i = 1; i < threads; i++) {
      level.set(threadId, i);
      victim.set(i, threadId);

      // Esperar hasta que sea el turno del hilo actual en todos los niveles anteriores
      boolean shouldWait = true;
      while (shouldWait) {
        shouldWait = false;
        for (int k = 0; k < threads; k++) {
          if (k != threadId && level.get(k) >= i && victim.get(i) == threadId) {
            shouldWait = true;
            break;
          }
        }
      }
    }
  }

  @Override
  public void unlock() {
    int threadId = ThreadID.get();

    // Reiniciar el nivel y la víctima del hilo actual
    level.set(threadId, 0);
    victim.set(threadId, 0);
  }
}
