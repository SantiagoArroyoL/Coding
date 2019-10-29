import java.util.Scanner;

/**
 * Clase para ...
 * @author ...
 */
public class Contestadora {
    
    //Estructura de la contestadora
    
    /**
     * Constructor de unca contestadora con capacidad para 10 mensajes
     */
    public Contestadora() {

    }

    /**
     * Constructor de una contestadora con capacidad para n mensajes
     * @param n - capacidad de la contestadora
     */
    public Contestadora(int n) {

    }

    /**
     *  Metodo que agrega un nuevo mensaje a la contestadora.
     *  @param nuevoMensaje Nuevo mensaje que sera agregado a la contestadora.
     */
    private void agregarMensaje(Mensaje nuevoMensaje){

    }
    
    /**
     *  Metodo que imprime en pantalla el contenido de la contestadora.
     */
    private void escucharMensajes(){
	    System.out.println("No hay mensajes nuevos");
    }
    
    
    /*
     * Metodo auxiliar para mostrar el menu de opciones
     * NO MODIFICARLO
     */
    private int menu(){
        Scanner in = new Scanner(System.in);

        int opcion = 0;
        boolean validacion = true;

        System.out.println("\nContestadora");
        System.out.println("1. Agregar mensaje");
        System.out.println("2. Revisar mensajes");
        System.out.println("3. Salir");
        System.out.print("Seleccionar una opcion  --> ");

	do{
	    opcion = 0;
            validacion = true;
            try{
                opcion = in.nextInt();
            }catch(Exception e){
                validacion = false;
            }
            if(opcion < 1 || opcion > 3){
                validacion = false;
                System.out.println("\nOpcion invalida.\nIntroduzca 1, 2 o 3.\n\n");
            }
	}while(!validacion);

        return opcion;
    }

    
    public static void main(String pps[]){
	//Programar el funcionamiento de la contestadora

    }
    
}
