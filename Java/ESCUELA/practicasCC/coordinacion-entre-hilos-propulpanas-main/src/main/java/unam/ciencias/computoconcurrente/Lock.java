package unam.ciencias.computoconcurrente;

/** This lock is used to achieve mutual exclusion */
public interface Lock {
  /**
   * The current thread acquires this lock. It might wait some time it the lock has been acquired by
   * another thread
   */
  void lock();
  /** The current thread releases the lock. This may allow another threads to acquire this lock. */
  void unlock();
}
