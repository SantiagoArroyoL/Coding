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
      int locks_in_level = PetersonTreeLockHelper.pow(i);
      for (int j = 0; j < locks_in_level; j++) {
        if (i == 0) {
          this.locks[index] = new PetersonLock(i, threads);
          index++;
        } else {
          this.locks[index] = new PetersonLock(i, threads);
          index++;
        }
      }
    }
  }

  @Override
  public void lock() {
    int threadId = this.getThreadID().get();
    int last = this.levels - 1;
    int parent_index = PetersonTreeLockHelper.getLockIndex(this.threads, last, threadId);
    for (int i = 0; i < this.levels; i++) {
      if (this.locks[parent_index] == null) {
        System.out.println(parent_index);
      }
      this.locks[parent_index].lock();
      last -= 1;
      parent_index = PetersonTreeLockHelper.getLockIndex(this.threads, last, threadId);
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

/*  PREGUNTAS
 *
 *   - Argumenta si la implementación de este lock es libre de hambruna.
 *     El candado de Peterson implementado como un árbol binario es libre de hambruna, ya que al usar
 *     candados de Peterson normales, y estos cumplir con la propiedad libre de hambruna, la propiedad se
 *     propaga inductivamente en cada candado del árbol por lo que globalmente tenemos la propiedad.
 *
 *   - Con tus propias palabras explica qué tan bueno es este algoritmo en términos de contención y coherencia de cachés.
 *     Podemos encontrar mucha contención en este algoritmo, ya que si un thread quiere adquirir un lock,
 *     tiene que pasar por todos los niveles del árbol y competir por el lock en cada nivel.
 *     En terminos de coherencia de cachés, esta se mantiene gracias a los candados de Peterson pero al tener
 *     mucha competencia, tenemos también mucha comunicación y sincronización lo que puede afectar el rendimiento.
 * */
