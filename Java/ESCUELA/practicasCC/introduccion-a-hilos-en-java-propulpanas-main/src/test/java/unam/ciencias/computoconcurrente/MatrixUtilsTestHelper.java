package unam.ciencias.computoconcurrente;

// import java.io.FileWriter;
// import java.io.IOException;
// import java.io.Writer;
// import java.util.Arrays;
import java.util.Random;

public class MatrixUtilsTestHelper {
  static Float fillMatrixAndReturnMinimumValue(Matrix<Float> result) {
    float min = Float.MAX_VALUE;
    Random random = new Random();
    for (int r = 0; r < result.getRows(); r++) {
      for (int c = 0; c < result.getColumns(); c++) {
        result.setValue(r, c, random.nextFloat());
        min = Math.min(min, result.getValue(r, c));
      }
    }
    return min;
  }

  // private void escribe(String ruta, int[][] matriz) throws IOException {
  //   try (Writer writer = new FileWriter(ruta)) {
  //     writer.write(matriz.length + "," + matriz[0].length + "\n");
  //     for (int[] fila : matriz) {
  //       String linea = Arrays.toString(fila);
  //       writer.write(linea.substring(1, linea.length() - 1).replaceAll(" ", "") + "\n");
  //     }
  //   } catch (IOException ioe) {
  //     throw new RuntimeException(ioe);
  //   }
  // }
}
