package unam.ciencias.computoconcurrente;

public class ColorHelper {
  public static final int MIN_COLOR = 0;
  public static final int MAX_COLOR = 255;

  public static int adjustColor(float color) {
    return adjustColor(Math.round(color));
  }

  public static int adjustColor(int color) {
    return getInRange(color, MIN_COLOR, MAX_COLOR);
  }

  public static int getInRange(int value, int minValue, int maxValue) {
    value = Math.max(value, minValue);
    value = Math.min(maxValue, value);
    return value;
  }
}
