package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

public class MatrixAdditionTest {

  MatrixAddition matrixAddition;
  int NUM_THREADS = 1;
  MatrixParser<Integer> parser = new MatrixParser<>();
  private static final String DIR = "matrix_addition/";

  @Test
  void addition1() throws Exception {
    matrixAddition = new MultiThreadedMatrixAddition(NUM_THREADS);
    Matrix<Integer> matrix = new Matrix<>(new Integer[][] {{60}});
    Matrix<Integer> additon = matrixAddition.add(matrix, matrix, (a, b) -> a + b);
    Matrix<Integer> result = new Matrix<>(new Integer[][] {{120}});
    assertEquals(additon, result);
  }

  @Test
  void addition2() throws Exception {
    matrixAddition = new MultiThreadedMatrixAddition(NUM_THREADS);
    Matrix<Integer> matrix =
        new Matrix<>(
            new Integer[][] {
              {60, 45},
              {81, 59}
            });
    Matrix<Integer> additon = matrixAddition.add(matrix, matrix, (a, b) -> a + b);
    Matrix<Integer> result =
        new Matrix<>(
            new Integer[][] {
              {120, 90},
              {162, 118}
            });
    assertEquals(additon, result);
  }

  @Test
  void addition3() throws Exception {
    matrixAddition = new MultiThreadedMatrixAddition(NUM_THREADS);
    Matrix<Integer> matrix =
        new Matrix<>(
            new Integer[][] {
              {60, 45, 10},
              {81, 59, 36},
              {12, 33, 49}
            });
    Matrix<Integer> additon = matrixAddition.add(matrix, matrix, (a, b) -> a + b);
    Matrix<Integer> result =
        new Matrix<>(
            new Integer[][] {
              {120, 90, 20},
              {162, 118, 72},
              {24, 66, 98}
            });
    assertEquals(additon, result);
  }

  @Test
  void addition1sqrt() throws Exception {
    matrixAddition = new MultiThreadedMatrixAddition(NUM_THREADS);
    Matrix<Integer> matrix = new Matrix<>(new Integer[][] {{60}});
    Matrix<Integer> addition =
        matrixAddition.add(matrix, matrix, (x, y) -> (int) Math.round(Math.sqrt(x * x + y * y)));
    Matrix<Integer> result = new Matrix<>(new Integer[][] {{85}});

    assertEquals(addition, result);
  }

  @Test
  void addition2sqrt() throws Exception {
    matrixAddition = new MultiThreadedMatrixAddition(NUM_THREADS);
    Matrix<Integer> matrix =
        new Matrix<>(
            new Integer[][] {
              {60, 45},
              {81, 59}
            });
    Matrix<Integer> addition =
        matrixAddition.add(matrix, matrix, (x, y) -> (int) Math.round(Math.sqrt(x * x + y * y)));
    Matrix<Integer> result =
        new Matrix<>(
            new Integer[][] {
              {85, 64},
              {115, 83}
            });
    assertEquals(addition, result);
  }

  @Test
  void addition3sqrt() throws Exception {
    matrixAddition = new MultiThreadedMatrixAddition(NUM_THREADS);
    Matrix<Integer> matrix =
        new Matrix<>(
            new Integer[][] {
              {60, 45, 10},
              {81, 59, 36},
              {12, 33, 49}
            });
    Matrix<Integer> addition =
        matrixAddition.add(matrix, matrix, (x, y) -> (int) Math.round(Math.sqrt(x * x + y * y)));
    Matrix<Integer> result =
        new Matrix<>(
            new Integer[][] {
              {85, 64, 14},
              {115, 83, 51},
              {17, 47, 69}
            });
    assertEquals(addition, result);
  }

  @Test
  void additionFile1Threads1() throws Exception {
    executeTestCaseAdd(1, 1);
  }

  @Test
  void additionFile1Threads2() throws Exception {
    executeTestCaseAdd(1, 2);
  }

  @Test
  void additionFile1Threads3() throws Exception {
    executeTestCaseAdd(1, 4);
  }

  @Test
  void additionFile1Threads4() throws Exception {
    executeTestCaseAdd(1, 8);
  }

  @Test
  void additionFile2Threads1() throws Exception {
    executeTestCaseAdd(2, 1);
  }

  @Test
  void additionFile2Threads2() throws Exception {
    executeTestCaseAdd(2, 2);
  }

  @Test
  void additionFile2Threads3() throws Exception {
    executeTestCaseAdd(2, 4);
  }

  @Test
  void additionFile2Threads4() throws Exception {
    executeTestCaseAdd(2, 8);
  }

  @Test
  void additionFile3Threads1() throws Exception {
    executeTestCaseAdd(3, 1);
  }

  @Test
  void additionFile3Threads2() throws Exception {
    executeTestCaseAdd(3, 2);
  }

  @Test
  void additionFile3Threads3() throws Exception {
    executeTestCaseAdd(3, 4);
  }

  @Test
  void additionFile3Threads4() throws Exception {
    executeTestCaseAdd(3, 8);
  }

  void executeTestCaseAdd(int testNumber, int threads) throws Exception {
    matrixAddition = new MultiThreadedMatrixAddition(threads);
    Matrix<Integer> matrixA = parser.parse(DIR + testNumber + "A.txt", Integer::valueOf);
    Matrix<Integer> matrixB = parser.parse(DIR + testNumber + "B.txt", Integer::valueOf);
    Matrix<Integer> matrixExpected = parser.parse(DIR + testNumber + "C.txt", Integer::valueOf);
    Matrix<Integer> matrixResult = matrixAddition.add(matrixA, matrixB, (x, y) -> x + y);
    assertEquals(matrixExpected, matrixResult);
  }

  @Test
  void additionSqrtFile1Threads1() throws Exception {
    executeTestCaseSqrtAdd(1, 1);
  }

  @Test
  void additionSqrtFile1Threads2() throws Exception {
    executeTestCaseSqrtAdd(1, 2);
  }

  @Test
  void additionSqrtFile1Threads3() throws Exception {
    executeTestCaseSqrtAdd(1, 4);
  }

  @Test
  void additionSqrtFile1Threads4() throws Exception {
    executeTestCaseSqrtAdd(1, 8);
  }

  @Test
  void additionSqrtFile2Threads1() throws Exception {
    executeTestCaseSqrtAdd(2, 1);
  }

  @Test
  void additionSqrtFile2Threads2() throws Exception {
    executeTestCaseSqrtAdd(2, 2);
  }

  @Test
  void additionSqrtFile2Threads3() throws Exception {
    executeTestCaseSqrtAdd(2, 4);
  }

  @Test
  void additionSqrtFile2Threads4() throws Exception {
    executeTestCaseSqrtAdd(2, 8);
  }

  @Test
  void additionSqrtFile3Threads1() throws Exception {
    executeTestCaseSqrtAdd(3, 1);
  }

  @Test
  void additionSqrtFile3Threads2() throws Exception {
    executeTestCaseSqrtAdd(3, 2);
  }

  @Test
  void additionSqrtFile3Threads3() throws Exception {
    executeTestCaseSqrtAdd(3, 4);
  }

  @Test
  void additionSqrtFile3Threads4() throws Exception {
    executeTestCaseSqrtAdd(3, 8);
  }

  void executeTestCaseSqrtAdd(int testNumber, int threads) throws Exception {
    matrixAddition = new MultiThreadedMatrixAddition(threads);
    Matrix<Integer> matrixA = parser.parse(DIR + testNumber + "A.txt", Integer::valueOf);
    Matrix<Integer> matrixB = parser.parse(DIR + testNumber + "B.txt", Integer::valueOf);
    Matrix<Integer> matrixExpected = parser.parse(DIR + testNumber + "CS.txt", Integer::valueOf);
    Matrix<Integer> matrixResult =
        matrixAddition.add(matrixA, matrixB, (x, y) -> (int) Math.round(Math.sqrt(x * x + y * y)));
    assertEquals(matrixExpected, matrixResult);
  }
}
