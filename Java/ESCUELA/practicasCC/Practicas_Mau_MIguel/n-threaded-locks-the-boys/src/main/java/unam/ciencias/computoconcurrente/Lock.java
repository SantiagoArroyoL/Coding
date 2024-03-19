package unam.ciencias.computoconcurrente;

import lombok.Data;
import lombok.Getter;

/** This lock is used to achieve mutual exclusion */
@Data
@Getter
public abstract class Lock {

  private ThreadID threadID = new ThreadID();
  /**
   * The current thread acquires this lock. It might wait some time it the lock has been acquired by
   * another thread
   */
  public abstract void lock(); // acquire

  /** The current thread releases the lock. This may allow another threads to acquire this lock. */
  public abstract void unlock(); // release
}
