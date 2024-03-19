package unam.ciencias.computoconcurrente;

/** Static Tree barrier. For simplicity, number of threads must have form (radix^k-1)/(radix - 1) */
public class StaticTreeBarrier implements Barrier {

  /**
   * Constructor
   *
   * @param size Number of threads. (For simplicity, must be (radix^k-1)/(radix-1).
   * @param radix tree fan-in
   */
  public StaticTreeBarrier(int size, int radix) {}

  /** Spin until all threads have reached the barrier. */
  public void await() {}
}
