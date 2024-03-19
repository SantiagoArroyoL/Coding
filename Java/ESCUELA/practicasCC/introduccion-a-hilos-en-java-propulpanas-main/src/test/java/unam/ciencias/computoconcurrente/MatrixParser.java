package unam.ciencias.computoconcurrente;

import java.io.IOException;
import java.util.List;
import java.util.function.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class MatrixParser<T> {

  public Matrix<T> parse(String nombreMatriz, Function<String, T> parser) {
    try (Stream<String> lines = LineReader.getLinesFromResourceFile(nombreMatriz)) {
      List<String> filas = lines.collect(Collectors.toList());
      String[] dimensiones = filas.remove(0).split(",");
      Matrix<T> matrix =
          new Matrix<>(Integer.parseInt(dimensiones[0]), Integer.parseInt(dimensiones[1]));

      int index = 0;
      for (String fila : filas) {
        String[] valores = fila.split(",");
        for (int i = 0; i < valores.length; i++) {
          matrix.setValue(index, i, parser.apply(valores[i]));
        }
        index++;
      }
      return matrix;
    } catch (IOException ioe) {
      throw new RuntimeException(ioe);
    }
  }
}
