package mx.unam.ciencias.edd.proyecto2;

import mx.unam.ciencias.edd.Lista;

/**
 * Clase encargada de manejar las banderas contenidas en el arreglo de entrada
 *
 * @author Arroyo Lozano Santiago
 * @version 1.0
 * @since 11/04/2020 - 28/04/2020.
 */
public class Banderas {

	/**
	 * Método que revisa si el arreglo recibido va a ser de la forma estándar o no
     * @param args el arreglo a revisar
     * @return true en caso de que sea una entrada estandar - false en caso contrario
     */
	public boolean checaEstandar(String[] args) {
		if (args.length == 0)
			return true;
		return false;
	}

	/**
	 * Método auxiliar que revisa si hay almohadillas en la línea que estamos revisando
	 * @param str Cadena a revisar
	 * @return true si contiene una almohadilla - false en caso contrario
	 */
	public boolean contieneAlmohadillas(String str) {
		return str.contains("#");
	}

	/**
	 * Método que transforma una cadena en una lista con elementos para la estructura
	 * @param cadena La cadena a diseccionar
	 * @return Una nueva lista de enteros pertenecientes a una estructura de datos a graficar
	 */
	public Lista<Integer> interpretaElementos(String cadena, String identificador) {
		String[] elementos = cadena.split(" ");
		Lista<Integer> nuevaLista = new Lista<>();
		for (int i = 1; i < elementos.length; i++) {
			try {
				// System.out.println("INDICE["+i+"] "+ elementos[i]);
				nuevaLista.agrega(Integer.parseInt(elementos[i]));
			} catch (NumberFormatException e) {
				/* Si se lanza esta excepción es porque o leímos una letra o un espacio en blanco
				 * Si es una letra mandamos error, puesto que en ninguna de las dos entrdas debe haber letras */
				if (!isBlank(elementos[i]) && !identificador.equals(elementos[i])) {
					System.err.println("Por favor introduce sólo números");
					System.exit(-1);
				}
			}
		}
		return nuevaLista;
	}
	
	/**
	 * Método que busca simular al método isBLank() de Java 11
	 * Este método nos dice si una cadena sólo tiene espacios o tabulaciones
	 * @param str La cadena a evaluar
	 * @return true si sólo tiene espacios - false en caso contrario
	 */
	public boolean isBlank(String str) {
    	return str == null || str.trim().isEmpty();
	}

}//Cierre de la clase Banderas
