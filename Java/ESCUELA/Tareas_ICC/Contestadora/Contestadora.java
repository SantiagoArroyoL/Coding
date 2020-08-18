import java.util.Scanner;
import java.util.InputMismatchException;

/**
 * Clase para ...
 * @author ...
 */
public class Contestadora {

   //Estructura de la contestadora
   private Mensaje [] mensajes;
   private int indice,opcion;

   /**
   *  Metodo menú
  */
   private void menu(){

      Scanner leer = new Scanner(System.in);
      opcion = 0;
      boolean validacion = true;

      System.out.println("-----------------");
      System.out.println("\nContestadora");
      System.out.println("-----------------");
      System.out.println("1. Agregar mensaje");
      System.out.println("2. Revisar mensajes");
      System.out.println("3. Salir");
      System.out.print("Seleccionar una opcion  --> ");

   	do {
         opcion = 0;
         validacion = true;
         try{
            opcion = leer.nextInt();
         } catch(InputMismatchException e){
            validacion = false;
            System.out.println("\nOpcion invalida.\nIntroduzca 1, 2 o 3.\n\n");
         }
         if(opcion < 1 || opcion > 3) {
            validacion = false;
            System.out.println("\nOpcion invalida.\nIntroduzca 1, 2 o 3.\n\n");
         }
   	} while(!validacion);

      switch (opcion) {
         case 1:{
            System.out.println("Por favor introduce el mensaje:");
            String mensajeAgregado = leer.nextLine();
            System.out.println("ORA");
            Mensaje nuevo = new Mensaje(mensajeAgregado);
            agregarMensaje(nuevo);
            break;
         }
         case 2:{
            escucharMensajes();
            break;
         }
         case 3:{
            System.exit(0);
         }
      }
   }

   /**
    * Constructor de unca contestadora con capacidad para 10 mensajes
    */
   public Contestadora() {
      mensajes = new Mensaje[10];
      menu();
   }

   /**
    * Constructor de una contestadora con capacidad para n mensajes
    * @param n - capacidad de la contestadora
    */
   public Contestadora(int n) {
      menu();
      indice = 0;
      mensajes = new Mensaje[(n>0) ? n:10];
   }

   /**
    *  Metodo que agrega un nuevo mensaje a la contestadora.
    *  @param nuevoMensaje Nuevo mensaje que sera agregado a la contestadora.
    */
   public void agregarMensaje(Mensaje nuevoMensaje) {
      if(this.indice == mensajes.length) {
         System.out.println("Ya no hay espacio");
         return;
      }
      if(nuevoMensaje == null) {
         System.out.println("El mensaje es nulo");
         return;
      }
      mensajes[indice++] = nuevoMensaje;
   }

    /**
     *  Metodo que imprime en pantalla el contenido de la contestadora.
     * Se imprimen los mensajes no nulos que no hayan sido escuchados.
     */
   public void escucharMensajes() {
      if(indice == 0){
         System.out.println("La contestadora está vacía");
         return;
      }
      for (int i=0;i < indice ; i++) {
         if(!mensajes[i].fueEscuchado()) {
            System.out.println(mensajes[i].escucha());
         }
      }
   }

   /**
    * Método que imprime en pantalla el mensaje más reciente
    */
   public void escucharMensaje() {
      if(indice == 0){
         System.out.println("La contestadora está vacía");
         return;
      }
      for (int i=indice-1;i>0; i--) {
         if(!mensajes[i].fueEscuchado()) {
            System.out.println(mensajes[i].escucha());
            break;
         }
      }
   }


   /**
    * Método para escuchar el mensaje en la posición i
    * @param i el índice del mensaje a escuchar.
    */
   public void escucharMensaje(int i) {
      if(indice == 0){
         System.out.println("La contestadora está vacía");
         return;
      }
      if(i >= 0 && i < indice) {
         System.out.println(mensajes[i].escucha());
      }else {
         System.out.println("No existe el mensaje: " + i);
      }
   }

   /**
    * Devuelve una cadena con todos los mensajes de la contestadora aunque
    * no hayan sido escuchados.
    * @return Una cadena con los mensajes.
    */
   public String toString() {
      String msjs = "";
      for (int i = 0;i < indice ;i++ ) {
         msjs += String.format("Mensaje %d: %s\n",i,mensajes[i].escucha());
      }
      return msjs;
   }
}
