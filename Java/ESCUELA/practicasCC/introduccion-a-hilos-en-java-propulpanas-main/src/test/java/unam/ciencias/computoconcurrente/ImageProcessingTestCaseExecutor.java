package unam.ciencias.computoconcurrente;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.is;
import static unam.ciencias.computoconcurrente.MatrixComparator.areSimilar;

public class ImageProcessingTestCaseExecutor {
  private static final boolean WRITE_RESULTS = false;
  private static final int EPSILON = 3;

  static <N extends ImageProcessingAlgorithm> void executeTestCase(
      N algorithm, String inputResource, String expectedOutputResource)
      throws InterruptedException {
    Image inputImage = Image.build(ImageIOHelper.loadImageFromResources(inputResource));
    Image expectedOutputImage =
        Image.build(ImageIOHelper.loadImageFromResources(expectedOutputResource));

    Image actualOutputImage = algorithm.process(inputImage);

    if (WRITE_RESULTS) {
      long timestamp = System.currentTimeMillis();
      ImageIOHelper.persistImageToResources(
          timestamp + "-" + expectedOutputResource,
          ImageFormat.PNG,
          Image.buildBufferedImage(actualOutputImage));
    }

    assertThat(areSimilar(actualOutputImage, expectedOutputImage, EPSILON), is(true));
  }
}
