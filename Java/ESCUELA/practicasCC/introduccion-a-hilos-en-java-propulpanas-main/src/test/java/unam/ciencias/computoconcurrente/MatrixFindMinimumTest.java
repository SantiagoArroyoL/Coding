package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

public class MatrixFindMinimumTest {
  MatrixFindMinimum matrixFindMinimum;

  @Test
  void findMinimum() throws Exception {
    matrixFindMinimum = new MultiThreadedMatrixFindMinimum();
    Matrix<Float> matrix =
        new Matrix<>(
            new Float[][] {
              {4f, 29f, -6f, 0f},
              {15f, 6f, 0f, 4f},
              {25f, 41f, -10f, 4f},
              {0f, 0f, -1f, 39f},
            });

    assertEquals(-10f, matrixFindMinimum.findMinimum(matrix));
  }

  @Test
  void findMinimumConcurrent() throws Exception {
    matrixFindMinimum = new MultiThreadedMatrixFindMinimum(2);
    Matrix<Float> matrix =
        new Matrix<>(
            new Float[][] {
              {4f, 29f, -6f, 0f},
              {15f, 6f, 0f, 4f},
              {25f, 41f, -10f, 4f},
              {0f, 0f, -1f, 39f},
            });

    assertEquals(-10f, matrixFindMinimum.findMinimum(matrix));
  }

  @Test
  void findMinimumBigMatrix() throws Exception {
    matrixFindMinimum = new MultiThreadedMatrixFindMinimum();
    int rows = 5000, columns = 1000;
    Matrix<Float> matrix = new Matrix<>(rows, columns);
    float minimum = MatrixUtilsTestHelper.fillMatrixAndReturnMinimumValue(matrix);
    assertEquals(minimum, matrixFindMinimum.findMinimum(matrix));
  }

  @Test
  void findMinimumConcurrentBigMatrix() throws Exception {
    matrixFindMinimum = new MultiThreadedMatrixFindMinimum(4);
    int rows = 5000, columns = 1000;
    Matrix<Float> matrix = new Matrix<>(rows, columns);
    float minimum = MatrixUtilsTestHelper.fillMatrixAndReturnMinimumValue(matrix);
    assertEquals(minimum, matrixFindMinimum.findMinimum(matrix));
  }
}
