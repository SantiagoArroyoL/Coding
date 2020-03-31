package mx.unam.ciencias.edd.proyecto1;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.io.IOException;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import mx.unam.ciencias.edd.Lista;

/**
 * Proyecto 1: Ordenador lexicografico.

 * Clase encargada de manejar un ordenador lexicográfico que funciona con uno o más archivos de texto
 * o la entrada estándar, que puede imprime su salida en la salida estándar, o en reversa.
 * Además de manera opcional puede crear un archivo con el nombre que el usuario decida
 * que contenga la salida del programa
 *
 * @author Arroyo Lozano Santiago
 * @version 1.0
 * @since 25/03/2020.
 */
public class Proyecto1 {

	/**
	 * Ordenador lexicográfico que funciona con uno o más archivos de texto o la entrada estándar
	 * Imprime su salida en la salida estándar, en reversa o en un archivo separado.
	 * @param args En args se recibirán las banderas y los archivos con los que trabajaremos
	 */
	public static void main(String[] args) {

		/* Esta cadena sólo nos ayudará para el constructor de la clase renglón */
		String temp;
		/* Clase que nos auxiliará con el manejo de banderas */
		Banderas bandera = new Banderas();
		/* Creamos una lista de renglones, clase que contiene los parámetros de comparación */
		Lista<Renglon> listaFinal = new Lista<>();

		boolean esEspecial = bandera.checaEspecial(args);
		boolean esReversa = bandera.checaReversa(args);
		boolean esEstandar = bandera.checaEstandar(args, esReversa, esEspecial);
		String identificador = bandera.getIdentificdor();

		if (!esEstandar) {
			/* Eliminamos las banderas y agregamos los elementos a una nueva lista */
			Lista<String> nuevoArg = bandera.eliminaBanderas(args);
			for (String archivo : nuevoArg)
				try {
					/* Aquí ocurre la magia. readLine() lee exactamente cada línea del archivo
					 (el cual abrimos con FileReader) Almacenaremos cada linea en la lista de renglones*/
					BufferedReader br = new BufferedReader(new FileReader(archivo));
					while ((temp = br.readLine()) != null)
						listaFinal.agrega(new Renglon(temp));
				} catch (IOException io) {
					System.out.println("No se encontró el archivo de entrada");
					System.exit(-1);
				}
		} else
			try {
				/*Para el caso de la entrada estándar, la cual es representada por el objeto System.in*/
				BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
				while ((temp = br.readLine()) != null)
					listaFinal.agrega(new Renglon(temp));
			} catch (IOException io) {
				System.out.println("Hubo un error al intentar leer lo que escribiste");
				System.exit(-1);
			}

		/* Dependiendo de el valor booleano de la bandera reversa aplicamos ese método en listaFinal
		    De todas maneras aplicamos mergeSort en ambos casos */
		listaFinal = esReversa ? listaFinal.mergeSort(listaFinal).reversa() : listaFinal.mergeSort(listaFinal);

		/* Si la bandera especial no está activada
		 con un iterador imprimimos en consola y terminamos*/
		if (!esEspecial) {
			for (Renglon r : listaFinal)
				System.out.println(r);
			System.exit(0);
		}

		/* En caso contrario creamos un nuevo archivo nombrado como quizo el usuario,
		 escribimos en él y terminamos */
		try {
			File nuevo = new File(identificador+".txt");
			FileWriter myWriter = new FileWriter(nuevo);
			for (Renglon r: listaFinal)
				myWriter.write(r.toString() + System.getProperty("line.separator"));
			myWriter.close();
	    } catch (IOException io) {
	    	System.out.println("Ocurrió un error");
	    	io.printStackTrace();
			System.exit(-1);
	    }
	}//Cierre del método main

}//Cierre de la clase Proyecto1
