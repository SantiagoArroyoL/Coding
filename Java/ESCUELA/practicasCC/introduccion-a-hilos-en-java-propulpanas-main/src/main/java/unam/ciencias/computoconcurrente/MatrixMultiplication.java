package unam.ciencias.computoconcurrente;

public interface MatrixMultiplication {
  Matrix<Integer> multiply(Matrix<Integer> matrixA, Matrix<Integer> matrixB)
      throws InterruptedException;
}
