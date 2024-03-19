package unam.ciencias.computoconcurrente;

public class TwoValueCounter extends FixedValueCounter {
  public TwoValueCounter() {
    super();
  }

  @Override
  public int getAndIncrement() {
    int id = ThreadID.get();
    int iteration = this.iteration.get();
    int rounds = this.rounds;

    int current = this.getValue();
    int next = current + 1;

    if (id == 0 && iteration == 0) {
      try {
        Thread.sleep(100);
      } catch (InterruptedException e) {
        throw new RuntimeException(e);
      }
    }

    if (id == 1 && iteration == 98) {
      try {
        Thread.sleep(100);
        this.value = next;
      } catch (InterruptedException e) {
        throw new RuntimeException(e);
      }
    }

    if (id == 1 && iteration == 99) {
      this.value = next;
      System.out.println("Ultima iteración 1: " + this.value);
    }

    if (id == 0 && iteration == 1) {
      this.value = next;
    }

    return next;
  }

  @Override
  public int getAndDecrement() {
    return 0;
  }
}
