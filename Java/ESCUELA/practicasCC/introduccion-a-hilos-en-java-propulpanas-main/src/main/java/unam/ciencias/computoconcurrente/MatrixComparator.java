package unam.ciencias.computoconcurrente;

import java.awt.Color;

public class MatrixComparator {

  public static boolean areSimilar(Matrix<Integer> matrix1, Matrix<Integer> matrix2, int sigma) {
    return areSimilar(
        matrix1,
        matrix2,
        (a, b, epsilon) -> {
          Color currentPixel1 = new Color(a);
          Color currentPixel2 = new Color(b);
          return isCloseTo(currentPixel1.getRed(), currentPixel2.getRed(), epsilon)
              && isCloseTo(currentPixel1.getGreen(), currentPixel2.getGreen(), epsilon)
              && isCloseTo(currentPixel1.getBlue(), currentPixel2.getBlue(), epsilon);
        },
        sigma);
  }

  public static boolean areSimilar(Matrix<Float> matrix1, Matrix<Float> matrix2, float sigma) {
    return areSimilar(matrix1, matrix2, MatrixComparator::isCloseTo, sigma);
  }

  public static <T> boolean areSimilar(
      Matrix<T> m1, Matrix<T> m2, ProximityComparator<T> comparator, float epsilon) {
    int rows = m1.getRows();
    int columns = m1.getColumns();
    if (rows != m2.getRows() || columns != m2.getColumns()) {
      return false;
    }
    for (int i = 0; i < rows; i++) {
      for (int j = 0; j < columns; j++) {
        if (!comparator.test(m1.getValue(i, j), m2.getValue(i, j), epsilon)) {
          return false;
        }
      }
    }
    return true;
  }

  private static boolean isCloseTo(float a, float b, float sigma) {
    float min = a - sigma;
    float max = a + sigma;
    return b > min && b < max;
  }
}
