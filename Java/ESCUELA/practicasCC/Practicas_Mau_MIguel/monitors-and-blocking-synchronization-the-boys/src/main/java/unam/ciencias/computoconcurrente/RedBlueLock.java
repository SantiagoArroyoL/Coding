package unam.ciencias.computoconcurrente;

import java.util.concurrent.locks.Lock;

public interface RedBlueLock {
  Lock getRedLock();
  Lock getBlueLock();
  int[] redAndBlueThreadCount();
}
