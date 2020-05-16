import java.util.Scanner;
public class Tablas{
	public static void main(String[] args) {

		//Variables
		boolean valido = false;
		Scanner pausa = new Scanner(System.in);
		Scanner puma = new Scanner(System.in);
		String entrada  ="";
		int c, temp, limite = 0;
		int n1 = 0;
		int n2 = 1;

		//Empieza la tarea uno
		System.out.println("Tarea 1, contador del 0 al 100 de 2 en 2");
		//Pausa
		//System.out.println("Presiona una tecla para continuar");
		do {
	    	entrada  = pausa.nextLine();
	    	System.out.println(entrada);
 		}
		while(!entrada.equals(""));
		for (c=0;c<=100;c = c + 2) {
			System.out.println(c);
		}
		System.out.println("------------------------------------------------------------------");

		//Pausa
		System.out.println("Presiona una tecla para continuar");
		do {
	    	entrada  = pausa.nextLine();
	    	System.out.println(entrada);
 		}
		while(!entrada.equals(""));


		//Empieza la tarea dos
		System.out.println("Tarea 2,contador del 1000 al 500 de 3 en 3");
		//Pausa
		//System.out.println("Presiona una tecla para continuar");
		do {
	    	entrada  = pausa.nextLine();
	    	System.out.println(entrada);
 		}
		while(!entrada.equals(""));
		for (c=1000;c>=500;c = c - 3) {
			System.out.println(c);
		}
		System.out.println("-----------------------------------------------------------------");
		//Pausa
		System.out.println("Presiona una tecla para continuar");
		do {
	    	entrada  = pausa.nextLine();
	    	System.out.println(entrada);
 		}
		while(!entrada.equals(""));
		System.out.println("-----------------------------------------------------------------");

		System.out.println("Tarea 3,la sucesion de Fibbonacci");
		//Pausa
		//System.out.println("Presiona una tecla para continuar");
		do {
	    	entrada  = pausa.nextLine();
	    	System.out.println(entrada);
 		}
		while(!entrada.equals(""));

		//Comienza la tarea 3
		System.out.println("Dime cuantos digitos de la sucesion quieres:");

		//Valida que lo que sea que hayan metido sea un número valido
		while (!valido) {
			try{
				limite = puma.nextInt();
				valido = true;
			} catch (Exception ex) {
				System.out.println("Este no es un numero valido");
				puma.next();
				continue;
			}
		}
		System.out.println("-----------------------------------------------------------------");

		System.out.println(n1);
		System.out.println(n2);
		for (c=0;c<=(limite - 3);c++) {
			//Temp solo guarda el valor de n2 temporalmente mientras n2 se acutliza con el valor de n1 + temp para imprimir
			temp = n1;
			n1 = n2;
			n2 = temp + n1;
			System.out.println(n2);
		}
	}
}
