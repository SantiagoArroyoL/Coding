import java.util.Scanner;
class pendiente{


  public static void main(String[] args) {

    int x1 = 10;
    int x2 = 10;
    int y1 = 10;
    int y2 = 10;

    Scanner puma1 = new Scanner(System.in);
    System.out.println("Ingresa x1: \n");
    x1 = puma1.nextInt();

    Scanner puma2 = new Scanner(System.in);
    System.out.println("Ingresa x2: \n");
    x2 = puma2.nextInt();

    Scanner puma3 = new Scanner(System.in);
    System.out.println("Ingresa y1: \n");
    y1 = puma3.nextInt();

    Scanner puma4 = new Scanner(System.in);
    System.out.println("Ingresa y2: \n");
    y2 = puma4.nextInt();

    float pen = (x1-x2)/(y1-y2);
    System.out.println(pen);

  }
}
