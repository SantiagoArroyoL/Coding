package unam.ciencias.computoconcurrente;

import java.util.ArrayList;
import java.util.List;
import java.util.function.IntBinaryOperator;

public class MultiThreadedMatrixAddition extends MultiThreadedOperation implements MatrixAddition {

  public MultiThreadedMatrixAddition() {
    super();
  }

  public MultiThreadedMatrixAddition(int threads) {
    super(threads);
  }

  @Override
  public Matrix<Integer> add(
      Matrix<Integer> matrixA, Matrix<Integer> matrixB, IntBinaryOperator operator)
      throws InterruptedException {
    int inicio = 0;
    int numRows = matrixA.getRows() / this.threads;
    int residuo = matrixA.getRows() % this.threads;
    List<Thread> threadList = new ArrayList<>(this.threads);
    Matrix<Integer> matrixC = new Matrix<>(matrixA.getRows(), matrixA.getColumns());
    for (int i = 0; i < this.threads; i++) {
      int fin = inicio + numRows + residuo;
      int finalInicio = inicio;
      threadList.add(
          new Thread(() -> taskAdd(finalInicio, fin, matrixA, matrixB, matrixC, operator)));
      inicio = fin;
      if (residuo > 0) {
        residuo -= 1;
      }
    }
    this.runAndWaitForThreads(threadList);
    return matrixC;
  }

  /**
   * Fila por fila
   *
   * @param inicio la fila inicial a sumar
   * @param fin la fila que ya no se va a sumar
   */
  private void taskAdd(
      int inicio,
      int fin,
      Matrix<Integer> matrixA,
      Matrix<Integer> matrixB,
      Matrix<Integer> matrixC,
      IntBinaryOperator operator) {
    for (int i = inicio; i < fin; i++) {
      for (int j = 0; j < matrixA.getColumns(); j++) {
        int suma = operator.applyAsInt(matrixA.getValue(i, j), matrixB.getValue(i, j));
        matrixC.setValue(i, j, suma);
      }
    }
  }
}
