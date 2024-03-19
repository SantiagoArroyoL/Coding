package unam.ciencias.computoconcurrente;

public class PetersonTreeLockHelper {
  public static int getLockID(int threads, int level, int threadId) {
    int locksInLevel = pow(level);
    int threadsPorLock = threads / locksInLevel;
    int groupSize = threadsPorLock / 2;

    return (threadId / groupSize) % 2;
  }

  public static int getLockIndex(int threads, int level, int threadId) {
    int locksInLevel = pow(level);
    int threadsPorLock = threads / locksInLevel;
    int groupSize = threadsPorLock / 2;

    return (threadId / threadsPorLock) + pow(level) - 1;
  }

  public static int discreteBaseTwoLogarithm(int num) {
    int log = 0;
    while (num > 1) {
      num /= 2;
      log++;
    }
    return log;
  }

  public static int pow(int num) {
    int res = 1;
    for (int i = 0; i < num; i++) {
      res *= 2;
    }
    return res;
  }
}
