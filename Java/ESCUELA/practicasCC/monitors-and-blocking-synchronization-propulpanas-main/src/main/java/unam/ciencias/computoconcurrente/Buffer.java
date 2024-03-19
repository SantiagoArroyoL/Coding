package unam.ciencias.computoconcurrente;

public interface Buffer<T> {
  /**
   * Regresa el tamaño del buffer.
   *
   * @return size
   */
  int size();

  /**
   * Agrega un elemento al buffer se bloquea si esta lleno
   *
   * @param item
   */
  void put(T item) throws InterruptedException;

  /**
   * Elimina un elemento del buffer; se bloquea si esta vacío.
   *
   * @return siguienteElemento
   */
  T take() throws InterruptedException;

  /**
   * Obtiene el número de elementos del buffer.
   *
   * @return contedoDeObjetos
   */
  int elements();
}
