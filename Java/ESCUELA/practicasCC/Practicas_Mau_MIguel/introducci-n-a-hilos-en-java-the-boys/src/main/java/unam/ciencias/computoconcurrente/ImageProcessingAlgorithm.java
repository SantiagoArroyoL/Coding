package unam.ciencias.computoconcurrente;

public interface ImageProcessingAlgorithm {
  Image process(Image image) throws InterruptedException;
}
