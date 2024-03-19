package unam.ciencias.computoconcurrente;

import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

public class LamportBakeryLock extends Lock {
  private final int threads;
  AtomicBoolean[] flag;
  AtomicInteger[] label;

  public LamportBakeryLock(int threads) {
    this.threads = threads;
    flag = new AtomicBoolean[threads];
    label = new AtomicInteger[threads];
    for (int i = 0; i < threads; i++) {
      flag[i] = new AtomicBoolean(false);
      label[i] = new AtomicInteger(0);
    }
  }

  @Override
  public void lock() {
    int threadId = this.getThreadID().get();
    flag[threadId].set(true);
    label[threadId].set(getMaxLabel() + 1);

    for (int i = 0; i < threads; i++) {
      if (i != threadId) {
        while (flag[i].get()
            && (label[threadId].get() > label[i].get()
                || (label[threadId].get() == label[i].get() && threadId > i))) {}
      }
    }
  }

  @Override
  public void unlock() {
    int threadId = this.getThreadID().get();
    flag[threadId].set(false);
  }

  private int getMaxLabel() {
    int maxLabel = Integer.MIN_VALUE;
    for (int i = 0; i < threads; i++) {
      int currentNumber = this.label[i].get();
      if (currentNumber > maxLabel) {
        maxLabel = currentNumber;
      }
    }
    return maxLabel;
  }
}

/*  PREGUNTAS
 *
 *   - Con tus propias palabras explica qué tan bueno es este algoritmo en términos de contención y coherencia de cachés.
 *
 *     No hay problema con la contención, ya que el algoritmo de Lamport Bakery asigna turnos a los threads de
 *     forma secuencial por lo que no se presenta mucha competencia.
 *     En términos de coherencia de cachés tampoco tenemos muchos problemas ya que los threads no tienen
 *     mucha necesidad de acceder a memoria compartida pues a pesar de que las banderas y los turnos son
 *     arreglos en memoria compartida, sólo acceden a su casilla correspondiente.
 *
 *   - Hay alguna manera de mejorar el rendimiento haciendo uso inteligente cache lines de la computadora?
 *
 *     El algoritmo de Lamport Bakery Lock no se beneficia directamente de las estrategias de optimización
 *     de caché, ya que su implementación se basa en números de turno y no involucra un acceso intensivo a
 *     variables compartidas o estructuras de datos complejas.
 *
 *   - Cómo hiciste para asegurar que se cumpla la relación happens-before es las escrituras a los arreglos de flag y label?
 *
 *     La relación happens-before en el algoritmo de Lamport Bakery se asegura a través de los turnos, los
 *     números de turno se utilizan para determinar el orden en el que los hilos pueden ingresar a la sección
 *     crítica. Así mismo, la relación "happens-before" en las escrituras a los arreglos de flag y label se
 *     establece mediante el orden en que los hilos realizan sus respectivas operaciones. En un contexto
 *     más aterrizado al código, se podría decir que es gracias a hacer los ciclos for sobre los arreglos
 *     al hacer lock, ya que así los cambios realizados por un hilo en los arreglos de flag y label sean visibles
 *     para otros hilos en el orden correcto.
 *
 * */
