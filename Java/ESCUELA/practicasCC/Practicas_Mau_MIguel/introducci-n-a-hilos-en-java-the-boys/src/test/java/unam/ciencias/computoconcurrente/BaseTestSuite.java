package unam.ciencias.computoconcurrente;

public class BaseTestSuite {
  public boolean hasFewerThanFourCores() {
    return Runtime.getRuntime().availableProcessors() < 4;
  }

  public boolean hasFewerThanEightCores() {
    return Runtime.getRuntime().availableProcessors() < 8;
  }

  public boolean hasNotDefaultCores() {
    return Runtime.getRuntime().availableProcessors() != 2
        && Runtime.getRuntime().availableProcessors() != 4
        && Runtime.getRuntime().availableProcessors() != 8;
  }
}
