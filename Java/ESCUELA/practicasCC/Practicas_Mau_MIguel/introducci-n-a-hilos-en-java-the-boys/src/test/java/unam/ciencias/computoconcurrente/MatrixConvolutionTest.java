package unam.ciencias.computoconcurrente;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.is;
import static unam.ciencias.computoconcurrente.MatrixComparator.areSimilar;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.DisabledIfEnvironmentVariable;

class MatrixConvolutionTest extends BaseTestSuite {

  private final int SIGMA = 5;
  private static final String DIR = "convolution_processing/";
  private static final String DIR_KERNEL = "gaussian_kernel/";
  private MatrixParser<Integer> parser = new MatrixParser<>();
  private MatrixParser<Float> parserFloat = new MatrixParser<>();
  private Image matrix =
      Image.build(ImageIOHelper.loadImageFromResources("image1-gaussian-blur.png"));

  @Test
  void sequentialSmallImageAndSquareKernel() throws Exception {
    Matrix<Float> kernel =
        new Matrix<>(
            new Float[][] {
              {1 / 9f, 1 / 9f, 1 / 9f},
              {1 / 9f, 1 / 9f, 1 / 9f},
              {1 / 9f, 1 / 9f, 1 / 9f}
            });
    smallCases(kernel, "SmallImageAndSquareKernel.txt");
  }

  @Test
  void sequentialSmallImageAndSingleRowKernel() throws Exception {
    Matrix<Float> kernel = new Matrix<>(new Float[][] {{1 / 3f, 1 / 3f, 1 / 3f}});
    smallCases(kernel, "SmallImageAndSingleRowKernel.txt");
  }

  @Test
  void sequentialSmallImageAndSingleColumnKernel() throws Exception {
    Matrix<Float> kernel = new Matrix<>(new Float[][] {{1 / 3f}, {1 / 3f}, {1 / 3f}});
    smallCases(kernel, "SmallImageAndSingleColumnKernel.txt");
  }

  void smallCases(Matrix<Float> kernel, String name) throws Exception {
    MultiThreadedMatrixConvolution convolver = new MultiThreadedMatrixConvolution(1);
    Matrix<Integer> matrix =
        new Matrix<>(
            new Integer[][] {
              {-15853823, -14601723, -13747706, -14598906},
              {-10275555, -10078434, -9881057, -9749217},
              {-8564436, -8630230, -8827609, -9156317},
              {-16055551, -16055551, -15990014, -15990014}
            });
    Image image = new Image(matrix);
    Matrix<Integer> convolved = convolver.convolve(image, kernel);
    Matrix<Integer> result = parser.parse(DIR + name, Integer::valueOf);
    assertThat(areSimilar(convolved, result, SIGMA), is(true));
  }

  @Test
  @DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
  void oneImageAndSingleColumnKernelTest1() throws Exception {
    notQuadraticKernelCases(1);
  }

  @Test
  @DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
  void twoImageAndSingleColumnKernelTest1() throws Exception {
    notQuadraticKernelCases(2);
  }

  @Test
  @DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
  @DisableIfHasFewerThanFourCores
  void fourImageAndSingleColumnKernelTest1() throws Exception {
    notQuadraticKernelCases(4);
  }

  @Test
  @DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
  @DisableIfHasFewerThanEightCores
  void eightImageAndSingleColumnKernelTest1() throws Exception {
    notQuadraticKernelCases(8);
  }

  void notQuadraticKernelCases(int threads) throws Exception {
    MultiThreadedMatrixConvolution convolver = new MultiThreadedMatrixConvolution(threads);
    Matrix<Integer> matrix = parser.parse(DIR + 1 + "Matrix.txt", Integer::valueOf);
    Image image = new Image(matrix);
    Matrix<Float> kernel = parserFloat.parse(DIR + 1 + "Kernel.txt", Float::valueOf);
    Matrix<Integer> convolved = convolver.convolve(image, kernel);
    Matrix<Integer> result = parser.parse(DIR + 1 + "Result.txt", Integer::valueOf);
    assertThat(areSimilar(convolved, result, SIGMA), is(true));
  }

  @Test
  void convolutionOneSingleThreaded() throws Exception {
    convolutionTestCase(1, "convolution1.txt");
  }

  @Test
  void convolutionTwoSingleThreaded() throws Exception {
    convolutionTestCase(2, "convolution2.txt");
  }

  @Test
  @DisableIfHasFewerThanFourCores
  void convolutionFourSingleThreaded() throws Exception {
    convolutionTestCase(4, "convolution3.txt");
  }

  @Test
  @DisableIfHasFewerThanEightCores
  void convolutionEightSingleThreaded() throws Exception {
    convolutionTestCase(8, "convolution4.txt");
  }

  void convolutionTestCase(int numberThreads, String nombre) throws Exception {
    Matrix<Float> kernel = parserFloat.parse(DIR_KERNEL + "radiusOne.txt", Float::valueOf);
    MultiThreadedMatrixConvolution convolver = new MultiThreadedMatrixConvolution(numberThreads);
    Matrix<Integer> convolved = convolver.convolve(matrix, kernel);
    Matrix<Integer> result = parser.parse(DIR + nombre, Integer::valueOf);
    assertThat(areSimilar(convolved, result, SIGMA), is(true));
  }
}
