package unam.ciencias.computoconcurrente;

public interface MatrixConsumer<T> {
  void accept(int row, int column, T value);
}
