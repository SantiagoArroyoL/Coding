package unam.ciencias.computoconcurrente;

import lombok.Getter;
import lombok.Setter;

/**
 * This particular implementation of a lock uses the Peterson's Algorithm which only work for two
 * concurrent threads at most.
 */
public class PetersonLock implements Lock {

  /**
   * La clase tendrá los atributos flag y victima que deben ser volátiles para que los threads
   * tengan visibilidad sobre estas variables (no son cacheadas y se leen directamente desde la
   * memoria)
   */
  private VolatileBoolean[]
      flag; // Para tener arreglos de volatile boolean se hace la clase VolatileBoolean

  private volatile int victima;

  public PetersonLock() {
    flag = new VolatileBoolean[] {new VolatileBoolean(false), new VolatileBoolean(false)};
  }

  @Override
  public void lock() {
    flag[ThreadID.get()].setValue(true);
    victima = ThreadID.get();
    while (victima == ThreadID.get() && flag[1 - ThreadID.get()].isValue()) {}
  }

  @Override
  public void unlock() {
    flag[ThreadID.get()].setValue(false);
  }
}

@Getter
@Setter
class VolatileBoolean {
  volatile boolean value;

  public VolatileBoolean(boolean value) {
    this.value = value;
  }
}
