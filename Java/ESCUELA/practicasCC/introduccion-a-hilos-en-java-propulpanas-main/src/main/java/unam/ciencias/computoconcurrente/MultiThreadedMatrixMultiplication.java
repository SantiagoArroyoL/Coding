package unam.ciencias.computoconcurrente;

import java.util.ArrayList;
import java.util.List;

public class MultiThreadedMatrixMultiplication extends MultiThreadedOperation
    implements MatrixMultiplication {

  public MultiThreadedMatrixMultiplication() {
    super();
  }

  public MultiThreadedMatrixMultiplication(int threads) {
    super(threads);
  }

  @Override
  public Matrix<Integer> multiply(Matrix<Integer> matrixA, Matrix<Integer> matrixB)
      throws InterruptedException {
    int inicio = 0;
    int numRows = matrixA.getRows() / this.threads;
    int residuo = matrixA.getRows() % this.threads;
    List<Thread> threadList = new ArrayList<>(this.threads);
    Matrix<Integer> matrixC = new Matrix<>(matrixA.getRows(), matrixB.getColumns());
    for (int i = 0; i < this.threads; i++) {
      int fin = inicio + numRows + residuo;
      int finalInicio = inicio;
      threadList.add(new Thread(() -> taskMultiply(finalInicio, fin, matrixA, matrixB, matrixC)));
      inicio = fin;
      if (residuo > 0) {
        residuo -= 1;
      }
    }
    this.runAndWaitForThreads(threadList);
    return matrixC;
  }

  private void taskMultiply(
      int inicio,
      int fin,
      Matrix<Integer> matrixA,
      Matrix<Integer> matrixB,
      Matrix<Integer> matrixC) {
    for (int i = inicio; i < fin; i++) {
      for (int j = 0; j < matrixB.getColumns(); j++) {
        int suma = 0;
        for (int k = 0; k < matrixA.getColumns(); k++) {
          suma += matrixA.getValue(i, k) * matrixB.getValue(k, j);
        }
        matrixC.setValue(i, j, suma);
      }
    }
  }
}
