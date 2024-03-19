package unam.ciencias.computoconcurrente;

import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.stream.Stream;

public class LineReader {

  public static Stream<String> getLinesFromResourceFile(String fileName) throws IOException {
    ClassLoader classLoader = MatrixParser.class.getClassLoader();
    URL resource = classLoader.getResource(fileName);
    if (resource == null) {
      throw new IllegalArgumentException("file not found! " + fileName);
    } else {
      try {
        return Files.lines(Paths.get(resource.toURI()));
      } catch (URISyntaxException e) {
        throw new RuntimeException(e);
      }
    }
  }
}
