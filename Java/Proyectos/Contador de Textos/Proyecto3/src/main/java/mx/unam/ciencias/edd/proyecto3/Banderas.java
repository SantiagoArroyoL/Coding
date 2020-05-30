package mx.unam.ciencias.edd.proyecto3;

import java.io.InputStream;
import mx.unam.ciencias.edd.Diccionario;

/** Proyecto 3: Ordenador de textos

* Esta clase es la encargada de revisar el arreglo args y hacer la mayor parte del conteo
*
* @author Arroyo Lozano Santiago
* @version 2.0
* @since 23/05/2020
*/
public class Banderas {

	/* Diccionario en el que agregamos las palabras contadas*/
	private Diccionario<String,Integer> conteo = new Diccionario<>();

	/* El directorio donde escribiremos los archivos */
	private String directorio;

	/**
	 * Método que interpreta un arreglo de cadenas, eliminando la bandera -o y el nombre
	 * del directorio dejando así sólo nombres de archivos
	 * Si no introducen directorio mandamos error
	 * @param args El arreglo a depurar
	 * @return un arreglo de cdenas depurado
	 */
	public String[] interpreta(String[] args) {
		try {
			int i, j;
			String[] temp = new String[args.length-2];
			for (j = i = 0; i < args.length; i++)
				if(args[i].equals("-o")) {
					directorio = args[++i];
				} else {
					temp[j++] = args[i];
				}
			return temp;
		} catch(ArrayIndexOutOfBoundsException aiobe) {
			System.err.println("Por favor introduce un directorio");
			System.exit(-1);
		}
		return args;
	}

	/**
	 * Método que cuenta cuántas palabras hay en una línea
	 * Dividimos una línea en palabras individuales usando un arreglo
	 * Agregamos al diccionario la palabra y las veces que se repitió
	 * @param temp La línea a revisar
	 */
	public void cuenta(String temp) {
		int repeticiones = 1;
		String[] palabras = temp.split(" ");
		for (int i = 0; i < palabras.length; i++) {
			Renglon uno = new Renglon(palabras[i]);
			for (int j = i+1; j < palabras.length; j++) {
				Renglon dos = new Renglon(palabras[j]);
				if (uno.compareTo(dos) == 0)  {
			   		repeticiones++;    //Si son iguales incrementamos el contador
			   		palabras[j]="0";   //Reemplazamos palabras reptidas por cero
			   	}
		   	}
		   	if (palabras[i] != "0")
			   	conteo.agrega(palabras[i],repeticiones); //Añadimos la palabra y su contador
		   	repeticiones  = 1;
		}
	}

	/**
	 * Método que regresa el conteo de cada palabra del archivo
	 * @return EL conteo contenido en un diccionario
	 */
	public Diccionario<String,Integer> getConteo() {
		return conteo;
	}

	/**
	 * Método que regresa el directorio donde guardaremos los archivos
	 * @return La cadena con el nombre y/o ruta del directorio
	 */
	public String getDirectorio() {
		return directorio;
	}

	public InputStream getRecurso() {
		return getClass().getResourceAsStream("styles.css");
	}

}//Cierre de la clase Banderas
