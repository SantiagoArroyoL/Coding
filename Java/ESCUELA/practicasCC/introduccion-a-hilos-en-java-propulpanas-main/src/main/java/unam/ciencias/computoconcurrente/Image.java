package unam.ciencias.computoconcurrente;

import java.awt.*;
import java.awt.image.BufferedImage;
import java.util.Arrays;

public class Image extends Matrix<Integer> {

  public Image(int width, int height) {
    super(height, width);
  }

  private Image(int width, int height, int[] data) {
    super(width, height, Arrays.stream(data).boxed().toArray(Integer[]::new));
  }

  public Image(Matrix<Integer> matrix) {
    super(matrix.getRows(), matrix.getColumns());
    matrix.forEach(this::setValue);
  }

  public Color getColorAt(int row, int column) {
    return new Color(getValue(row, column));
  }

  public void setColorAt(int row, int column, Color color) {
    setValue(row, column, color.getRGB());
  }

  public static Image build(BufferedImage image) {
    int width = image.getWidth();
    int height = image.getHeight();
    int[] data = new int[width * height];
    image.getRGB(0, 0, width, height, data, 0, width);
    return new Image(width, height, data);
  }

  public static BufferedImage buildBufferedImage(Image image) {
    BufferedImage bufferedImage =
        new BufferedImage(image.getColumns(), image.getRows(), BufferedImage.TYPE_INT_RGB);
    image.forEach((r, c, value) -> bufferedImage.setRGB(c, r, value));
    return bufferedImage;
  }
}
