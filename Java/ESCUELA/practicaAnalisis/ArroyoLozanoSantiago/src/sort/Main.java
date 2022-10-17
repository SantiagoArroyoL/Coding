package sort;

public class Main {

  public static void main(String[] args) {
    if (args.length == 3) {
      String archivo = args[0];
      int framerate = Integer.parseInt(args[1]);
      String algoritmo = args[2];
      new Sort(archivo, framerate, algoritmo);
    } else {
      System.err.println("(-)\tFavor de ejecutar con los argumentos correspondientes desde la carpeta 'src'");
      System.err.println("\t\t Ejemplo: java sort.Main imagen1 60 bubble");
    }
  }

}
