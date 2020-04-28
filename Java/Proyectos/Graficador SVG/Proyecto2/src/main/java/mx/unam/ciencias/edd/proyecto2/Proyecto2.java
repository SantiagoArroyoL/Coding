package mx.unam.ciencias.edd.proyecto2;

import java.io.IOException;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import mx.unam.ciencias.edd.Lista;

/**
 * Proyecto 2: Graficador SVG

 * Programa que grafica las estructuras de datos vistas en el curso
 * El nombre y comportamiento de dichas estructruas está dado por
 * los archivos del paquete mx.unam.ciencias.edd
 * El programa puede recibir un archivo a través de la entrada estándar y de la entrada no estándar
 * Las líneas que contengan almohadillas serán ignoradas,
 * al igual que los espacios, saltos de línea y tabulaciones.
 * La actual implementación sólo permite estructuras que contengan números enteros.
 * La salida será el codigo XML necesario para crear el SVG que represente la estructura de datos
 * Esto incluye también los datos necesarios para generar un documento XML
 * Esta clase en particular sólo tiene un método main encargado de la lectura de la entrada
 * y manda a llamar a la clase Graficador
 *
 * @author Arroyo Lozano Santiago
 * @version 1.0
 * @since 11/04/2020 - 28/04/2020.
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
		/* Este arreglo contiene cómo se deben escribir las clases válidas para graficar */
		String[] clasesValidas = new String[]{"Lista", "Pila", "Cola", "Arreglos", "ArbolBinarioCompleto", "ArbolBinarioOrdenado", "ArbolRojinegro", "ArbolAVL", "MonticuloMinimo", "Grafica"};

		if (!esEstandar) {
			for (int i = 0; i < args.length; i++)
				if (!bandera.contieneAlmohadillas(args[i]))
					cadena += args[i] + " ";
		} else {
			try {
				BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
				while ((temp = br.readLine()) != null)
					if (!bandera.contieneAlmohadillas(temp))
						cadena += temp + " ";
				br.close();
			}
			catch (IOException ioe) {
				System.err.println("Ocurrió un error al tratar de abrir el archivo.");
				System.exit(-1);
			}
			/* identificamos la clase */
			for (int i = 0; i < clasesValidas.length; i++)
				if (cadena.contains(clasesValidas[i]))
					identificador = clasesValidas[i];
		}

		/* Creamos un graficador que, valga la redundancia, graficará la clase que reciba */
		Graficador graficador = new Graficador(identificador);
		/* Aquí comienza la magia de graficar el SVG */
		Lista<Integer> listaFinal = bandera.interpretaElementos(cadena, esEstandar);
		if (listaFinal.esVacia()) {
			System.err.println("Por favor introduce una estructura no vacía");
			System.exit(-1);
		}
		/* Revisamos que la lista tenga número par de elementos para las graficas */
		if (identificador.equals("Grafica") && listaFinal.getElementos() % 2 != 0) {
			System.err.println("Por favor introduce un número par de elementos");
			System.exit(-1);
		}
		String dibujo = graficador.graficaColeccion(listaFinal);
		System.out.println(dibujo);
	}//Cierre del método main
}//Cierre de la clase Proyecto1
