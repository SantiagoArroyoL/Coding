package unam.ciencias.computoconcurrente;

public abstract class FixedValueCounter implements Counter {
  protected volatile int value;
  protected ThreadLocal<Integer> iteration;
  protected int rounds;

  public FixedValueCounter() {
    this.value = 0;
    this.iteration = ThreadLocal.withInitial(() -> 0);
    this.rounds = 0;
  }

  public void setIteration(int iteration) {
    this.iteration.set(iteration);
  }

  public void setRounds(int rounds) {
    this.rounds = rounds;
  }

  @Override
  public int getValue() {
    return this.value;
  }
}
