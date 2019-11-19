/**
 * Este programa simula una epidemia y un incendio forestal usando los automatass celulares y la POO
 * En esta clase le solicitaremos al usuario un valor de tiempo en milisegundos para controlar la frecuencia en la que se genera cada generación de Células
 * Tambien solicitamos al usuario qué Simulación le gustaría observar, ya se Epidemia o Incendio
 * @author: Arroyo Lozano Santiago
 * @version: 12/Sept/19 A
 */
import java.util.Scanner;
import java.util.InputMismatchException;
public abstract class Automatas {
	private static int tiempoF;
	private static int x;
	private static int y;
   private static String simulacion;


	public static void main(String[] args) {

		//Declaramos los objetos y sus respectivos valores
		Scanner leer = new Scanner(System.in);
      String Incendio = new String("Incendio");
      String Epidemia = new String("Epidemia");

      //El siguiente bloque Try and Catch nos asegura que el usuario solo puede introducir valores enteros positivos, gracias a las Excepciónes de tipo InputMismatchException e IllegalArgumentException
      try{
         System.out.println("¿Qué simulación quieres correr?\n Epidemia o Incendio");
         simulacion = leer.nextLine();

         System.out.println("¿Qué valor de x(Alto) le quieres dar a tu simulación?");
         x = leer.nextInt();

         System.out.println("¿Qué valor de y(Ancho) le quieres dar a tu simulación?");
         y = leer.nextInt();

         System.out.println("¿Qué tan rápido quieres que cambien las generaciones? (Escribe el valor en milisegundos)");
         tiempoF = leer.nextInt();

         if (tiempoF < 0 || x < 0 || y < 0) {
            System.out.println("Por favor ingresa números mayores a 0, intentalo de nuevo");
            System.exit(0);
         }

      }catch (InputMismatchException e) {
         //Para que solo escriban números enteros
         System.out.println("Por favor ingresa sólo números enteros, intentalo de nuevo");
         System.exit(0);

      }finally{
         if (Incendio.equals(simulacion) || Epidemia.equals(simulacion)) {
            System.out.println("Generando simulación de " + x + "x" + y + " pixeles y " + tiempoF + " milisegundos");
         }else {
            System.out.println("No ingresaste como se debía el nombre de la simulación, intentalo de nuevo");
            System.exit(0);
         }
      }

   	//Llamamos al objeto GUI (Graphic User Interface)
   	GUI gui = new GUI(x,y,simulacion);
   	gui.Reloj(tiempoF,simulacion);

	}//Cierre de el metodo main
}//Cierre de la clase
