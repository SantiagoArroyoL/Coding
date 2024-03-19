package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.DisabledIfEnvironmentVariable;

public class SobelOperatorTest {
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
        new MultiThreadedSobelOperator(threads), "image1.png", "image1-sobel-operator.png");
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
        new MultiThreadedSobelOperator(threads), "image2.png", "image2-sobel-operator.png");
  }

  @Test
  void mediumImageSingleThreaded() throws Exception {
    executeTestCaseForMediumImageTwo(1);
  }

  @Test
  void mediumImageTwoThreaded() throws Exception {
    executeTestCaseForMediumImageTwo(2);
  }

  @Test
  void mediumImageFourThreaded() throws Exception {
    executeTestCaseForMediumImageTwo(4);
  }

  @Test
  void mediumImageEightThreaded() throws Exception {
    executeTestCaseForMediumImageTwo(8);
  }

  void executeTestCaseForMediumImageTwo(int threads) throws Exception {
    ImageProcessingTestCaseExecutor.executeTestCase(
        new MultiThreadedSobelOperator(threads),
        "medium-image.png",
        "medium-image-sobel-operator.png");
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
        new MultiThreadedSobelOperator(threads), "huge-image.png", "huge-image-sobel-operator.png");
  }
}
