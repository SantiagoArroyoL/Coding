/**
* Clase que lee el CSV y genera una Lista de Arreglos
* @author Arroyo Lozano Santiago
* @version 11/11/2019 A
*/
package practica14;
import java.io.IOException;
import java.util.List;
import java.util.LinkedList;
import java.nio.file.Files;
import java.nio.file.Paths;

public class LectorCSV {

	/**
	 * Método que lee un archivo CSV y de su contenido genera coordenadas x, y
	 * El método diferencia entre cadenas vacías y cadenas que no sean de números
	 * @param ruta La ruta del archivo CSV a leer
	 * @return Una lista de arreglos que contienen las coordenadas
	 */
	public static List<String[]> leer(String ruta) throws IOException {

		List<String> lineas = Files.readAllLines(Paths.get(ruta));
		List<String[]> arregloLineas = new LinkedList<>();

		for (String i : lineas) {
			String[] aRevisar = i.trim().split(", ");
			if (esNumero(aRevisar[0]) && esNumero(aRevisar[1])){
				arregloLineas.add(aRevisar);
			}
		}
		return arregloLineas;
	}

	/**
	 * Método que verifica si la variable puede ser transformada a double o no
	 * @param cadena La cadena a examinar
	 * @return true si se puede convertir a double - false en caso contrario
	 */
	public static boolean esNumero(String cadena) throws NumberFormatException{
		try {
			Double.parseDouble(cadena);
			return true;
		} catch(NumberFormatException e) {
			return false;
		}
	}

}
