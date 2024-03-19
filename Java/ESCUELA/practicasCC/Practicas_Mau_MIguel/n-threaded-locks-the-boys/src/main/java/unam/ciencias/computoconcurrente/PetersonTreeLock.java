package unam.ciencias.computoconcurrente;

public class PetersonTreeLock extends Lock {
  private final int threads;
  private final Lock[] locks;

  private final int levels;

  public PetersonTreeLock(int threads) {
    this.threads = threads;
    this.locks = new Lock[threads - 1];
    this.levels = PetersonTreeLockHelper.discreteBaseTwoLogarithm(threads);
    int index = 0;
    for (int i = 0; i < this.levels; i++) {
      int locksInLevel = PetersonTreeLockHelper.pow(i);
      for (int j = 0; j < locksInLevel; j++) {
        this.locks[index] = new PetersonLock(i, threads);
        index++;
      }
    }
  }

  @Override
  public void lock() {
    int threadId = this.getThreadID().get();
    int last = this.levels - 1;
    int parentIndex = PetersonTreeLockHelper.getLockIndex(this.threads, last, threadId);
    for (int i = 0; i < this.levels; i++) {
      if (this.locks[parentIndex] == null) {
        System.out.println(parentIndex);
      }
      this.locks[parentIndex].lock();
      last -= 1;
      parentIndex = PetersonTreeLockHelper.getLockIndex(this.threads, last, threadId);
    }
  }

  @Override
  public void unlock() {
    int threadId = this.getThreadID().get();
    for (int i = 0; i < this.levels; i++) {
      int index = PetersonTreeLockHelper.getLockIndex(this.threads, i, threadId);
      this.locks[index].unlock();
    }
  }
}
