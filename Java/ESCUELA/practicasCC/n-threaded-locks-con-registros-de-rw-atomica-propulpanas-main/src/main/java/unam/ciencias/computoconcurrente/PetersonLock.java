package unam.ciencias.computoconcurrente;

/**
 * This particular implementation of a lock uses the Peterson's Algorithm which only work for two
 * concurrent threads at most.
 */
public class PetersonLock extends Lock {

  private final VolatileBoolean[] flag;
  private volatile int victim;
  private final int level;
  private final int threads;

  public PetersonLock(int level, int threads) {
    this.flag = new VolatileBoolean[] {new VolatileBoolean(false), new VolatileBoolean(false)};
    this.level = level;
    this.threads = threads;
  }

  @Override
  public void lock() {
    int threadId = this.getThreadID().get();
    int lockID = PetersonTreeLockHelper.getLockID(threads, this.level, threadId);
    this.flag[lockID].setValue(true);
    this.victim = threadId;
    while (isOtherThreadAlsoContending(threadId) && isVictim(threadId)) {}
  }

  private boolean isOtherThreadAlsoContending(int threadId) {
    int lockID = PetersonTreeLockHelper.getLockID(threads, this.level, threadId);
    return this.flag[1 - lockID].isValue();
  }

  private boolean isVictim(int threadId) {
    return this.victim == threadId;
  }

  @Override
  public void unlock() {
    int threadId = this.getThreadID().get();
    int lockID = PetersonTreeLockHelper.getLockID(threads, this.level, threadId);
    this.flag[lockID].setValue(false);
  }
}
