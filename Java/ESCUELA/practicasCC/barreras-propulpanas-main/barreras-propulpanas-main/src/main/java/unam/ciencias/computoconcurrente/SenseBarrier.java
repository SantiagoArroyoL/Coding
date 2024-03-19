/*
 * SenseBarrier.java
 *
 * Created on August 3, 2005, 10:49 PM
 *
 * From "Multiprocessor Synchronization and Concurrent Data Structures",
 * by Maurice Herlihy and Nir Shavit.
 * Copyright 2006 Elsevier Inc. All rights reserved.
 */

package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Sense-reversing barrier
 *
 * @author Maurice Herlihy
 */
public class SenseBarrier implements Barrier {
  AtomicInteger count; // how many threads have arrived
  final int size; // number of threads
  volatile boolean sense; // object's sense
  ThreadLocal<Boolean> threadSense;

  /** Constructor */
  public SenseBarrier(int n) {
    count = new AtomicInteger(n);
    size = n;
    sense = false;
    threadSense = ThreadLocal.withInitial(() -> !sense);
  }
  /** Wait for threads to catch up. */
  public void await() { // ~TTAS
    boolean mySense = threadSense.get();
    int position = count.getAndDecrement(); // --
    if (position == 1) { // I'm last
      count.set(this.size); // reset counter
      sense = mySense; // reverse sense
    } else {
      while (sense != mySense) {} // busy-wait
    }
    threadSense.set(!mySense);
  }
}
