import java.util.Scanner;
import java.util.InputMismatchException;
/**
 * Programa que solicita un número de cuenta y lo muestra con su letra adicional.
 * @author Arroyo Lozano Santiago
 * @version 12/10/2019 A
 */
public class numCta{

	public static void main(String[] args) {
		/* Variables,arreglo y Scanner necesesarios para el programa */
		int n, c, tNumCta;
		String sNumCta = "", numeroCuenta = "";
		Scanner leer = new Scanner(System.in);
		char[] codigo = new char[]{'T', 'R', 'W', 'A', 'G', 'M', 'Y', 'F', 'P', 'D', 'X', 'B', 'N', 'J', 'Z', 'S', 'Q', 'V', 'H', 'L', 'C', 'K', 'E'};

		try {
			//Le pedimos al usuario su número de cuenta
			System.out.print("Dar el número de cuenta: ");
			tNumCta = leer.nextInt();
			sNumCta = String.valueOf(tNumCta);

			//Codificamos
			c = tNumCta % 23;
			numeroCuenta = sNumCta + codigo[c];

		} catch (InputMismatchException e) {
         //Usamos try-catch para que sólo escriban números enteros, evitando errores
         System.out.println("Por favor ingresa sólo números enteros, intentalo de nuevo");
         System.exit(0);
      } finally {
			//Comprobamos que sea un número de cuenta válido
			n = sNumCta.length();
			if (n != 8) {
				System.out.println("No es un número de cuenta válido");
			} else {
				System.out.println("El número de cuenta \"con código\" es: " + numeroCuenta);
			}
		}
	}//Cierre del main

}//Cierre de la clase
