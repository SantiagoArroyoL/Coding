package ajedrez.piezas;

import java.io.Serializable;

/**
 * Clase que representa la posición de cada pieza.
 *
 * @author Arroyo Lozano Santiago
 * @version 22/10/2019 A
 */
public class Posicion implements Serializable {
	private int fila;
	private int columna;

	/**
	 * Crea una matriz de mxn donde todas las entradas son cero.
	 * @param fila donde ese encuentra la pieza
	 * @param columna donde se encuentra l apieza
	 */
	public Posicion(int fila, int columna) {
		this.fila = fila;
		this.columna = columna;
	}//Cierre del método

	/**
	 * Método para obtener la fila de la Pieza
	 * @return fila donde se encuentra la Pieza
	 */
	public int obtenerFila() {
		return fila;
	}//Cierre del método

	/**
	 * Método para obtener la columna de la Pieza
	 * @return columna donde se encuentra la Pieza
	 */
	public int obtenerColumna() {
		return columna;
	}//Cierre del método

	/**
	 * Método para obtener la columna de la Pieza
	 * @param obj El objeto a comparar
	 * @return Verdadero si son iguales, falso si no lo son
	 */
	@Override
	public boolean equals(Object obj) {
      if (this == obj) {
         return true;
      }

		if (obj == null || getClass() != obj.getClass()) {
         return false;
      }
		Posicion otra = (Posicion) obj;
		return fila == otra.fila && columna == otra.columna;
	}

}//Cierre de la clase
