package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.DisabledIfEnvironmentVariable;

public class GaussianBlurTest {

  private static final int RADIUS = 5;

  @Test
  void imageOneSingleThreaded() throws Exception {
    executeTestCaseForImageOne(1);
  }

  @Test
  void imageOneTwoThreaded() throws Exception {
    executeTestCaseForImageOne(2);
  }

  @Test
  void imageOneFourThreaded() throws Exception {
    executeTestCaseForImageOne(4);
  }

  @Test
  void imageOneEightThreaded() throws Exception {
    executeTestCaseForImageOne(8);
  }

  void executeTestCaseForImageOne(int threads) throws Exception {
    ImageProcessingTestCaseExecutor.executeTestCase(
        new MultiThreadedGaussianBlur(threads, RADIUS), "image1.png", "image1-gaussian-blur.png");
  }

  @Test
  void imageTwoSingleThreaded() throws Exception {
    executeTestCaseForImageTwo(1);
  }

  @Test
  void imageTwoTwoThreaded() throws Exception {
    executeTestCaseForImageTwo(2);
  }

  @Test
  void imageTwoFourThreaded() throws Exception {
    executeTestCaseForImageTwo(4);
  }

  @Test
  void imageTwoEightThreaded() throws Exception {
    executeTestCaseForImageTwo(8);
  }

  void executeTestCaseForImageTwo(int threads) throws Exception {
    ImageProcessingTestCaseExecutor.executeTestCase(
        new MultiThreadedGaussianBlur(threads, RADIUS), "image2.png", "image2-gaussian-blur.png");
  }

  @Test
  void mediumImageSingleThreaded() throws Exception {
    executeTestCaseForMediumImage(1);
  }

  @Test
  void mediumImageTwoThreaded() throws Exception {
    executeTestCaseForMediumImage(2);
  }

  @Test
  void mediumImageFourThreaded() throws Exception {
    executeTestCaseForMediumImage(4);
  }

  @Test
  void mediumImageEightThreaded() throws Exception {
    executeTestCaseForMediumImage(8);
  }

  void executeTestCaseForMediumImage(int threads) throws Exception {
    ImageProcessingTestCaseExecutor.executeTestCase(
        new MultiThreadedGaussianBlur(threads, 20), "hd-image.png", "hd-image-gaussian-blur.png");
  }

  @DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
  @Test
  void hugeImageSingleThreaded() throws Exception {
    executeTestCaseForHugeImage(1);
  }

  @DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
  @Test
  void hugeImageTwoThreaded() throws Exception {
    executeTestCaseForHugeImage(2);
  }

  @DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
  @Test
  void hugeImageFourThreaded() throws Exception {
    executeTestCaseForHugeImage(4);
  }

  @DisabledIfEnvironmentVariable(named = "ENV", matches = "github")
  @Test
  void hugeImageEightThreaded() throws Exception {
    executeTestCaseForHugeImage(8);
  }

  void executeTestCaseForHugeImage(int threads) throws Exception {
    ImageProcessingTestCaseExecutor.executeTestCase(
        new MultiThreadedGaussianBlur(threads, 30),
        "huge-image.png",
        "huge-image-gaussian-blur.png");
  }
}
