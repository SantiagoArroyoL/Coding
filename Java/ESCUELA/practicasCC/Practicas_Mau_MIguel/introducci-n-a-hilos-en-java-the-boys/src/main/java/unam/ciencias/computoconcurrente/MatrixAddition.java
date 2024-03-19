package unam.ciencias.computoconcurrente;

import java.util.function.IntBinaryOperator;

public interface MatrixAddition {
  Matrix<Integer> add(Matrix<Integer> matrixA, Matrix<Integer> matrixB, IntBinaryOperator add)
      throws InterruptedException;
}
