package unam.ciencias.computoconcurrente;

public interface MatrixFindMinimum {
  <N extends Comparable<N>> N findMinimum(Matrix<N> matrix) throws InterruptedException;
}
