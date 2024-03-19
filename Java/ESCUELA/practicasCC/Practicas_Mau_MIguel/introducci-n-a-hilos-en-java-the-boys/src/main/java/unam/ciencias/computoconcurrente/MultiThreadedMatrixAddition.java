package unam.ciencias.computoconcurrente;

import java.util.function.IntBinaryOperator;
import java.util.ArrayList;

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
    if (matrixA.getRows() == matrixB.getRows() && matrixA.getColumns() == matrixB.getColumns()) {
      int hilos = Math.min(matrixA.getRows(), threads);
      int filas = matrixA.getRows() / hilos;

      Matrix<Integer> matrixC = new Matrix<>(matrixA.getRows(), matrixA.getColumns());

      ArrayList<Thread> listaHilos = new ArrayList<>();
      for (int i = 0; i < hilos; i++) {

        int filaInicio = i * filas;
        int filaFin;
        if (i == hilos - 1) {
          filaFin = matrixA.getRows();
        }else{
          filaFin = (i + 1) * filas;
        }

        int finalFilaFin = filaFin;
        Thread thread = new Thread(() -> {
          for (int k = filaInicio; k < finalFilaFin; k++) {
            for (int j = 0; j < matrixA.getColumns(); j++) {
              matrixC.setValue(k, j, operator.applyAsInt(matrixA.getValue(k, j), matrixB.getValue(k, j)));
            }
          }
        });

        listaHilos.add(thread);
      }
      this.runAndWaitForThreads(listaHilos);

      return matrixC;
    }else{
      throw new IllegalArgumentException("ERROR: Deben coincidir las matrices en sus dimensiones");
    }
  }
}
