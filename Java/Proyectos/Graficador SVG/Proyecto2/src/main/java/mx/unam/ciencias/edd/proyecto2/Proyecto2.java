package mx.unam.ciencias.edd.proyecto2;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.io.IOException;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.InputStream;
import java.io.FileInputStream;
import mx.unam.ciencias.edd.*;

/**
 * Proyecto 2: Graficador SVG

 * Clase encargada de manejar *****************************
 *
 * @author Arroyo Lozano Santiago
 * @version 1.0
 * @since 11/04/2020.
 */
public class Proyecto2 {

	public static void main(String[] args) {

		/* Cadenas auxiliares que nos ayudarán a leer el archivo y almacenar su contenido */
		String temp = "", cadena = "";
		/* Clase que nos auxiliará con el manejo de banderas */
		Banderas bandera = new Banderas();
		/* Revisamos si la entrada es de la forma estándar o no */
		boolean esEstandar = bandera.checaEstandar(args);
		/* Identificamos con qué clase estamos trabajando */
		bandera.identifica(args);
		String identificador = bandera.getIdentificador();

		if (!esEstandar) {
			for (int i = 0; i < args.length; i++)
				if (!bandera.contieneAlmohadillas(args[i]))
					cadena += args[i] + " ";
		} else {
			try {
				/*Para el caso de la entrada estándar, la cual es representada por el objeto System.in*/
				BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
				while ((temp = br.readLine()) != null)
				if (!bandera.esIdentificador(temp)) {
					if (!bandera.contieneAlmohadillas(temp))
						cadena += temp;
				} else {
					identificador = temp;
				}
			} catch (IOException io) {
				System.out.println("Hubo un error al intentar leer lo que escribiste");
				System.exit(-1);
			}
		}

		/* Creamos un graficador que, valga la redundancia, graficará la clase que reciba */
		Graficador graficador = new Graficador(identificador);
		/* Aquí comienza la magia de graficar el SVG */
		Lista<Integer> listaFinal = bandera.interpretaElementos(cadena);
		if (listaFinal.esVacia()) {
			System.err.println("Por favor introduce una estructura no vacía");
		} else {
			String dibujo = graficador.graficaColeccion(listaFinal);
			System.out.println(dibujo);
		}
	}//Cierre del método main
}//Cierre de la clase Proyecto1
