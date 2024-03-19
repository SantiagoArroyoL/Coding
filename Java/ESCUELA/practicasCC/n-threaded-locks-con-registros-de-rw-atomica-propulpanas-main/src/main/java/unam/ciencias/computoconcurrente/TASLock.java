package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicBoolean;

public class TASLock extends Lock {

  private final AtomicBoolean state;

  public TASLock() {
    state = new AtomicBoolean(false);
  }

  @Override
  public void lock() {
    while (state.getAndSet(true)) {}
  }

  @Override
  public void unlock() {
    state.set(false);
  }
}
