/* Autor: Arroyo Lozano Santiago
   Fecha: 22/Agosto/2019
   practica04
 */

import java.util.Scanner;

public class RFC {

	public static void main(String[] args) {
		Scanner scanner = new Scanner(System.in);
		String nombre = new String();
		String año, mes, dia, apellidoM, apellidoP, inicial;
	    String fecha = new String();
		int x;

		System.out.println("Introduce tu nombre completo:");
		nombre = scanner.nextLine();

		System.out.println("Introduce tu fecha de nacimiento en formato dd/mm/aaaa:");
		fecha  = scanner.nextLine();

		//CREACIÓN DEL RFC

		//Apellido Paterno
		x = nombre.indexOf(" ");
		apellidoP =  nombre.substring(x+1,x+3);
		//Apellido Materno
		x = nombre.lastIndexOf(" ");
		apellidoM = nombre.substring(x+1,x+2);
		//Inicial del nombre
		x = 0;
		inicial = nombre.substring(x,x+1);

		//Año
		x = 6;
		año = fecha.substring(x+2,x+4);
		//Mes
		x = fecha.indexOf("/");
		mes = fecha.substring(x+1,x+3);
		//Día
		x = 0;
		dia = fecha.substring(x,x+2);
		String RFC = apellidoP + apellidoM + inicial + año + mes + dia;
		RFC = RFC.toUpperCase();
		System.out.println("El RFC de " +  nombre + " es: " + RFC);


	}

}
