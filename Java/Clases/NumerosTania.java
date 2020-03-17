import java.util.Scanner;

public class NumerosTania {
	public static void main(String[] args) {

		int entrada, longitud;
		Scanner leer = new Scanner(System.in);

		System.out.println("Escribe el número que quieres mostrar como texto");
		entrada = leer.nextInt();

		longitud = cuenta(entrada);
		System.out.println(convertidor(longitud, entrada));

	}//Cierre método main


	public static String convertidor(int longitud, int entrada) {

		String cadenaFinal = "";
		int i = 0, temp = entrada;
		int[] arr = new int[longitud];

		/*Nuestro banco de palabras dividido en cuatro arreglos*/
		String[] centenas = new String[]{"cien", "doscientos", "trescientos", "cuatroscientos", "quinientos", "seiscientos", "setecientos", "ochocientos","novecientos"};

		String[] decenas = new String[]{"diez", "veinte", "treinta", "cuarenta", "cincuenta", "sesenta", "setenta", "ochenta", "noventa"};

		String[] unidades = new String[]{"cero", "uno", "dos", "tres", "cuatro", "cinco", "seis", "siete", "ocho", "nueve"};

		/*Dividimos cada digito del número en un arreglo*/
		while (temp > 0) {
		    arr[i] = temp % 10;
		    temp = temp / 10;
			i++;
		}

		/*Finalmente creamos la cadena final*/
		switch (longitud) {
			case 1: cadenaFinal = unidades[entrada]; break;
			case 2: cadenaFinal = decenas[arr[1]-1] + " y " + unidades[arr[0]]; break;
			case 3: cadenaFinal = centenas[arr[2]-1] + " " +  decenas[arr[1]-1] + " y " +  unidades[arr[0]]; break;
			case 4: cadenaFinal = unidades[arr[3]] + " mil " + centenas[arr[2]-1] + " " +  decenas[arr[1]-1] + " y " +  unidades[arr[0]]; break;
			case 5: cadenaFinal = decenas[arr[4]-1] + " y " + unidades[arr[3]] + " mil " + centenas[arr[2]-1] + " " +  decenas[arr[1]-1] + " y " +  unidades[arr[0]]; break;
			case 6: cadenaFinal = centenas[arr[5]-1] + " " + decenas[arr[4]-1] + " y " + unidades[arr[3]] + " mil " + centenas[arr[2]-1] + " " +  decenas[arr[1]-1] + " y " +  unidades[arr[0]]; break;
			case 7: cadenaFinal = unidades[arr[6]] + " millones " + centenas[arr[5]-1] + " " + decenas[arr[4]-1] + " y " + unidades[arr[3]] + " mil " + centenas[arr[2]-1] + " " +  decenas[arr[1]-1] + " y " +  unidades[arr[0]]; break;
		}
		return cadenaFinal;
	}//Cierre del método convertidor

	public static int cuenta(int entrada)  {
		//Con el siguiente if sabemos de cuántos digiitos es el número
		if (entrada < 100000) {
		    if (entrada < 100) {
		        if (entrada < 10) {
		            return 1;
		        } else {
		            return 2;
		        }
		    } else {
		        if (entrada < 1000) {
		            return 3;
		        } else {
		            if (entrada < 10000) {
		                return 4;
		            } else {
		                return 5;
		            }
		        }
		    }
		} else {
		    if (entrada < 10000000) {
		        if (entrada < 1000000) {
		            return 6;
		        } else {
		            return 7;
		        }
		    } else {
		        if (entrada < 100000000) {
		            return 8;
		        } else {
		            if (entrada < 1000000000) {
		                return 9;
		            } else {
		                return 10;
		            }
		        }
		    }
		}//Cierre de los if
	}//Cierre del método cuenta

}
