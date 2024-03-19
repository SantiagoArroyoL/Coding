package unam.ciencias.computoconcurrente;

import java.util.concurrent.locks.Lock;

public interface ReadWriteLock {
  Lock readLock();

  Lock writeLock();
}
