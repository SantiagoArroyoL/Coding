package unam.ciencias.computoconcurrente;

import java.awt.*;
import java.util.ArrayList;
import java.util.List;

public class MultiThreadedMatrixConvolution extends MultiThreadedOperation
    implements MatrixConvolution {

  public MultiThreadedMatrixConvolution() {
    super();
  }

  public MultiThreadedMatrixConvolution(int threads) {
    super(threads);
  }

  @Override
  public Image convolve(Image image, Matrix<Float> kernel) throws InterruptedException {
    Image r = new Image(image.getColumns(), image.getRows());
    List<Thread> threadList = new ArrayList<>(this.threads);

    int numRows = image.getRows() / this.threads;
    int residuo = image.getRows() % this.threads;
    int yInicio = 0;
    for (int i = 0; i < this.threads; i++) {
      int yFinal = yInicio + numRows + residuo;
      int finalYInicio = yInicio;
      threadList.add(new Thread(() -> taskConvolve(image, kernel, finalYInicio, yFinal, r)));
      if (residuo > 0) {
        residuo -= 1;
      }
      yInicio = yFinal;
    }
    this.runAndWaitForThreads(threadList);
    return r;
  }

  private void taskConvolve(
      Image image, Matrix<Float> kernel, int y_inicio, int y_final, Image result) {
    int kw = kernel.getColumns();
    int kh = kernel.getRows();
    int w = image.getColumns();
    int h = image.getRows();

    for (int i = y_inicio; i < y_final; i++) {
      for (int j = 0; j < w; j++) {
        double r = 0.0, g = 0.0, b = 0.0;
        for (int kernelY = 0; kernelY < kh; kernelY++) {
          for (int kernelX = 0; kernelX < kw; kernelX++) {
            int imageX = Math.min(Math.max(j + (kernelX - kw / 2), 0), w - 1);
            int imageY = Math.min(Math.max(i + (kernelY - kh / 2), 0), h - 1);

            Color color = image.getColorAt(imageY, imageX);
            r += color.getRed() * kernel.getValue(kernelY, kernelX);
            g += color.getGreen() * kernel.getValue(kernelY, kernelX);
            b += color.getBlue() * kernel.getValue(kernelY, kernelX);
          }
        }
        Color ncolor =
            new Color(
                Math.min(Math.max((int) r, 0), 255),
                Math.min(Math.max((int) g, 0), 255),
                Math.min(Math.max((int) b, 0), 255));
        result.setColorAt(i, j, ncolor);
      }
    }
  }
}
