package unam.ciencias.computoconcurrente;


import java.util.ArrayList;

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
    if (matrixA.getColumns() == matrixB.getRows()) {
      Matrix<Integer> matrixC = new Matrix<>(matrixA.getRows(), matrixB.getColumns());
      int hilos = (matrixA.getRows()<threads) ? matrixA.getRows() : threads;
      int filas = matrixA.getRows() / hilos;

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
          for (int j = filaInicio; j < finalFilaFin; j++) {
            for (int k = 0; k < matrixC.getColumns(); k++) {
              int t = 0;
              for (int l = 0; l < matrixA.getColumns(); l++) {
                t += matrixA.getValue(j, l) * matrixB.getValue(l, k);
              }
              matrixC.setValue(j, k, t);
            }
          }
        });
        listaHilos.add(thread);
      }
      this.runAndWaitForThreads(listaHilos);

      return matrixC;
    }else{
      throw new IllegalArgumentException("ERROR: las dimensiones no coinciden");
    }
  }
}
