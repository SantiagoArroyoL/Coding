package unam.ciencias.computoconcurrente;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.equalTo;
import static org.hamcrest.Matchers.is;

import org.junit.jupiter.api.Test;

class MatrixMultiplicationTest {
  MatrixMultiplication matrixMultiplication;
  MatrixParser<Integer> parser = new MatrixParser<>();
  private static final String DIR = "matrix_multiplication/";

  @Test
  void sequentialSingleEntry() throws Exception {
    matrixMultiplication = new MultiThreadedMatrixMultiplication();
    Matrix<Integer> m1 = new Matrix<>(new Integer[][] {{2}});
    Matrix<Integer> m2 = new Matrix<>(new Integer[][] {{9}});
    Matrix<Integer> expected = new Matrix<>(new Integer[][] {{18}});
    Matrix<Integer> result = matrixMultiplication.multiply(m1, m2);
    assertThat(result, is(equalTo(expected)));
  }

  @Test
  void sequentialSmallSquareMatrix() throws Exception {
    executeTestCase(0, 1);
  }

  /** Matrices de (2x3)x(3x4) - 1 */
  @Test
  void sequentialMultiply2x3x4() throws Exception {
    executeTestCase(1, 1);
  }

  /** Matrices de (2x5)x(5x10) - 2 */
  @Test
  void sequentialMultiply2x5x10() throws Exception {
    executeTestCase(2, 1);
  }

  /** Matrices de (12x4)x(4x18) - 3 */
  @Test
  void multiply12x4x18() throws Exception {
    executeTestCase(3, 1);
  }

  /** Matrices de (12x4)x(4x18) - 4 */
  @Test
  void multiply20x6x21() throws Exception {
    executeTestCase(4, 1);
  }

  /** Matrices de (30x10)x(10x12) - 5 */
  @Test
  void sequentialMultiply30x10x12() throws Exception {
    executeTestCase(5, 1);
  }

  @Test
  void twoThreadedMultiply30x10x12() throws Exception {
    executeTestCase(5, 2);
  }

  @Test
  void fourThreadedMultiply30x10x12() throws Exception {
    executeTestCase(5, 4);
  }

  @Test
  void eightThreadedMultiply30x10x12() throws Exception {
    executeTestCase(5, 8);
  }

  /** Matrices de (2000x40)x(40x130) - 6 */
  @Test
  void sequentialMultiply2000x40x130() throws Exception {
    executeTestCase(6, 1);
  }

  @Test
  void twoThreadedMultiply2000x40x130() throws Exception {
    executeTestCase(6, 2);
  }

  @Test
  void fourThreadedMultiply2000x40x130() throws Exception {
    executeTestCase(6, 4);
  }

  @Test
  void eightThreadedMultiply2000x40x130() throws Exception {
    executeTestCase(6, 8);
  }

  void executeTestCase(int testNumber, int threads) throws Exception {
    matrixMultiplication = new MultiThreadedMatrixMultiplication(threads);
    Matrix<Integer> matrixA = parser.parse(DIR + testNumber + "A.txt", Integer::valueOf);
    Matrix<Integer> matrixB = parser.parse(DIR + testNumber + "B.txt", Integer::valueOf);
    Matrix<Integer> expectedResult = parser.parse(DIR + testNumber + "C.txt", Integer::valueOf);
    Matrix<Integer> matrixResult = matrixMultiplication.multiply(matrixA, matrixB);
    assertThat(matrixResult, is(equalTo(expectedResult)));
  }
}
