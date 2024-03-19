package unam.ciencias.computoconcurrente;

import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import javax.imageio.ImageIO;

public class ImageIOHelper {
  private static final String INPUT_DIR = "src/test/resources/image_processing/";
  private static final String OUTPUT_DIR = "src/test/resources/output_image_processing/";

  public static BufferedImage loadImageFromResources(String resourcePath) {
    try {
      String filePath = INPUT_DIR + resourcePath;
      File file = new File(filePath);
      return ImageIO.read(file);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  public static void persistImageToResources(
      String resourcePath, ImageFormat format, BufferedImage image) {
    try {
      String destPath = OUTPUT_DIR + resourcePath;
      File file = new File(destPath);
      ImageIO.write(image, format.toString(), file);
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }
}
