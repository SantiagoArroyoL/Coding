package unam.ciencias.computoconcurrente;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class FairRedBlueLock implements RedBlueLock {
  private Lock redLock;
  private Lock blueLock;
  private Lock lock;

  private int redWaiters = 0;
  private int blueWaiters = 0;
  private int redThreads = 0;
  private int blueThreads = 0;
  private boolean isRedTurn = true;

  private final ThreadID threadID;
  private final Condition redTurn;
  private final Condition blueTurn;

  public FairRedBlueLock() {
    this.redThreads = 0;
    this.blueThreads = 0;
    this.isRedTurn = false;
    this.redLock = new RedLock();
    this.blueLock = new BlueLock();
    this.threadID = new ThreadID();
    this.lock = new ReentrantLock();
    this.redTurn = this.lock.newCondition();
    this.blueTurn = this.lock.newCondition();
  }

  @Override
  public Lock getRedLock() {
    return this.redLock;
  }

  @Override
  public Lock getBlueLock() {
    return this.blueLock;
  }

  @Override
  public int[] redAndBlueThreadCount() {
    return new int[]{redThreads, blueThreads};
  }

  private class RedLock implements Lock {
    @Override
    public void lock() {
      lock.lock();
      try {
        redWaiters++;
        while ((blueThreads > 0 || !isRedTurn) && blueWaiters > 0) {
          redTurn.await();
        }
        redWaiters--;
        redThreads++;
      } catch (InterruptedException e) {
        Thread.currentThread().interrupt();
      } finally {
        lock.unlock();
      }
    }

    @Override
    public void unlock() {
      lock.lock();
      try {
        redThreads--;
        if (redThreads == 0 && redWaiters == 0) {
          isRedTurn = false;
          blueTurn.signalAll();
        }
      } finally {
        lock.unlock();
      }
    }

    @Override
    public void lockInterruptibly() throws InterruptedException {
      // TODO: implementation not required
    }

    @Override
    public boolean tryLock() {
      // TODO: implementation not required
      return false;
    }

    @Override
    public boolean tryLock(long time, TimeUnit unit) throws InterruptedException {
      // TODO: implementation not required
      return false;
    }

    @Override
    public Condition newCondition() {
      // TODO: implementation not required
      return null;
    }
  }

  private class BlueLock implements Lock {
    @Override
    public void lock() {
      lock.lock();
      try {
        blueWaiters++;
        while ((redThreads > 0 || isRedTurn) && redWaiters > 0) {
          blueTurn.await();
        }
        blueWaiters--;
        blueThreads++;
      } catch (InterruptedException e) {
        Thread.currentThread().interrupt();
      } finally {
        lock.unlock();
      }
    }


    @Override
    public void unlock() {
      lock.lock();
      try {
        blueThreads--;
        if (blueThreads == 0 && blueWaiters == 0) {
          isRedTurn = true;
          redTurn.signalAll();
        }
      } finally {
        lock.unlock();
      }
    }

    @Override
    public void lockInterruptibly() throws InterruptedException {
      // TODO: implementation not required
    }

    @Override
    public boolean tryLock() {
      // TODO: implementation not required
      return false;
    }

    @Override
    public boolean tryLock(long time, TimeUnit unit) throws InterruptedException {
      // TODO: implementation not required
      return false;
    }



    @Override
    public Condition newCondition() {
      // TODO: implementation not required
      return null;
    }
  }
}
