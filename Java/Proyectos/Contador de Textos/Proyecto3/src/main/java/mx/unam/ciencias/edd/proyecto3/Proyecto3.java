package mx.unam.ciencias.edd.proyecto3;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.FileNotFoundException;
import mx.unam.ciencias.edd.*;

/**
 * Proyecto 3: Ordenador de textos

 * Programa que recibe uno o varios archivos de texto, cuenta las palabras que estos tienen y crea archivos html
 * con toda la información y dibujos sobre gráfcias de barras, de pastel, arbolesRojinegros y arbolesAVL
 * en un directorio especificado por la bandera -o.
 * Nuestra herramienta más podersa será un Diccionario para cada archivo, en el cual la llave es la palabra y
 * su valor será un número entero indicando cuántas veces se repite. El diccionario nos permite mantener la complejidad
 * lo más sencilla que se pueda, ya que agregar(), eliminar(), contiene() y get() tienen complejidad constante.
 * Contaremos cada palabra y la añadiremos al diccionario, guardando en un arreglo de enteros el número
 * total de palabras en todo el archivo. Después guardaremos en una lista el diaccionario para más tarde
 * revisar si tiene palabras en común con los otrso diccionarios.
 * Finalmente nuestra clase graifcador es la encargada de dibujar los archivos html con los respectivos graficos
 *
 * Esta clase (Proyecto3) es la encargada de leer los archivos y llamar a las clases que realizarán el conteo
 * También creamos el directorio y los archivos para posteriormente escribir en ellos el dibujo creado por la clase
 * graficador.
 *
 * @author Arroyo Lozano Santiago
 * @version 1.0
 * @since 23/05/2020
 */
public class Proyecto3 {



	public static void main(String[] args) {

		/* Con el BufferedReader procesaremos el archivo (Por omisión lo construímos con la entrada estándar)*/
		BufferedReader br = null;
		/* Cadenas auxiliares que nos ayudarán a leer el archivo, almacenar su contenido y hacer la gráfica*/
		String temp = "", cadena = "", grafica = "";
		/* Clase que nos auxiliará con el manejo de banderas */
		Banderas bandera = new Banderas();
		/* Eliminamos la bandera y directoria de args */
		args = bandera.interpreta(args);
		/* Contador de palabras de cada archivo */
		int[] totales = new int[args.length];
		/* Inicializamos nuestro directorio */
		String directorio = bandera.getDirectorio();
		/* Graficador que hará la gráfica y todo lo demás */
		Graficador graficador = new Graficador("Grafica");
		/* Diccionario que usaremos para comparar palabras en común */
		Diccionario<String,Integer> conteo = new Diccionario<>();
		/* Lista de los diccionarios usados para cada archivo */
		Lista<Diccionario<String,Integer>> totalDic = new Lista<>();
		String path;
		File arch;
		FileWriter myWriter;

		/* Esto para cada archivo en args */
		for (int i = 0; i < args.length; i++) {
			/* Hay que buscar el archivo */
			bandera = new Banderas();
			try {
				br = new BufferedReader(new FileReader(args[i]));
			} catch (FileNotFoundException fnfe) {
				System.err.println("No se encontró el archivo");
				System.exit(-1);
			}
			/* Leemos el archivo y contamos */
			try {
				while ((temp = br.readLine()) != null)
					bandera.cuenta(temp);
				br.close();
			} catch (IOException ioe) {
				System.err.println("Ocurrió un error al tratar de leer el archivo.");
				System.exit(-1);
			}
			/* Vemos el conteo, graficamos, creamos y escribimos el archivo */
			Diccionario<String,Integer> d = bandera.getConteo();
			totalDic.agrega(d);
			String dibujo = graficador.dibujaHTML(d,i+1);
			try {
				path = directorio+"/archivo"+(i+1)+".html";
				File dir = new File(directorio);
				dir.mkdirs();
				arch = new File(path);
				myWriter = new FileWriter(path);
				myWriter.write(dibujo);
				myWriter.close();
			} catch (IOException e) {
				System.err.println("Ocurrió un error al crear o escribir el directorio o archivo");
				System.exit(-1);
			}
			totales[i] = graficador.suma();
		}
		/* Saliendo del for creamos el index y terminamos */
		br = new BufferedReader(new InputStreamReader(bandera.getRecurso()));
		path = directorio+"/styles.css";
		arch = new File(path);
		try {
			myWriter = new FileWriter(path);
			while ((temp = br.readLine()) != null)
				myWriter.write(temp);
			myWriter.close();
		} catch (IOException ioe) {
			System.err.println("Ocurrió un error al tratar de crear la hoja de estilos.");
			System.exit(-1);
		}
		try {
			path = directorio+"/index.html";
			arch = new File(path);
			myWriter = new FileWriter(path);
			myWriter.write(graficador.dibujaIndex(totales,totalDic));
			myWriter.close();
		} catch (IOException e) {
			System.err.println("Ocurrió un error al crear o escribir el archivo");
			System.exit(-1);
		}
	}//Cierre del método main
}//Cierre de la clase Proyecto3
