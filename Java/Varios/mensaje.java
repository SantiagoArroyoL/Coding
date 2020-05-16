import java.util.Scanner;
class mensaje{

  public static void main(String[] args){
    int edad = 17;

    System.out.println("Hola Mundo \n Yo soy Santiago Arroyo, soy un \"hombre\" que tiene " + edad);

    //Otra manera ed poner las variables literal
    int rosa = 7;
    System.out.printf("La variable rosa vale: %d",rosa);

    int var = 13;
    System.out.println("\n" + var);

    Scanner puma = new Scanner(System.in);
    System.out.println("Ingresa un número entero: \n");
    rosa = puma.nextInt();
    System.out.println("El nuevo valor de Rosa es:" + rosa);


  }
}
