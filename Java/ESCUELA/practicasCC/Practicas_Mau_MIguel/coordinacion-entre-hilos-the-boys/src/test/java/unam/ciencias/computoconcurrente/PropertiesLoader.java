package unam.ciencias.computoconcurrente;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

public class PropertiesLoader {
  static final Properties props = new Properties();

  static {
    try (InputStream inputStream =
        PropertiesLoader.class.getClassLoader().getResourceAsStream("application.properties")) {
      props.load(inputStream);
    } catch (IOException e) {
      e.printStackTrace(System.out);
    }
  }

  public static boolean getBooleanProperty(String key) {
    return Boolean.parseBoolean(props.getProperty(key, "false"));
  }
}
