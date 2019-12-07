/**
 * Ok, esta va estar buena xd
 * No quiero hacer una clase para cada tipo de pieza xd pero creo que eso tendremos que hacer o no se
 * En esta clase manejaremos la rotación de todas las piezas
 * Un método que mueve las piezas derecha o izquierda
 * Un método para caer de una casillas en una casilla (matriz 'cells' de la clase casillas)
 * Un método para caer de jalón
 * Cada pieza va a tener un valor entero, equivalente a los puntos
 *
 * @author Santi y Clau ^^
 */
package tetris;
import java.io.Serializable;
import tetris.Malla;
import java.util.Random;


public class Tetramino implements Serializable {

	private int fila, columna;
	private boolean[][] espacio = new boolean[4][4];


	/**
	 * Constructor de los tetraminos dependiendo del tipo que sean
	 * Le damos la forma de cada tetramino para los 6 tipos de pieza que hay en el juego
	 */
	public Tetramino (int tipo) {
		switch (tipo) {

			// I
			case 0 : {
				for (int i = 0; i < 4; i++) {
					for (int j = 0; j < 4; j++) {
						espacio[i][j] = (i == 1) ? true : false;
					}
				}
				break;
			}

			// J
			case 1 : {
				for (int i = 0; i < 4; i++) {
					for (int j = 0; j < 4; j++) {
						espacio[i][j] = (i == 1 && j < 3) ? true : false;
					}
				}
				espacio[0][0] = true;
				break;
			}

			// L
			case 2 : {
				for (int i = 0; i < 4; i++) {
					for (int j = 0; j < 4; j++) {
						espacio[i][j] = (i == 1 && j > 0) ? true : false;
					}
				}
				espacio[3][3] = true;
				break;
			}

			// O
			case 3 : {
				for (int i = 0; i < 4; i++) {
					for (int j = 0; j < 4; j++) {
						espacio[i][j] = ((i == 0 || i == 1 ) && (j == 1 || j == 2)) ? true : false;
					}
				}
				break;
			}

			// S
			case 4 : {
				for (int i = 0; i < 4; i++) {
					for (int j = 0; j < 4; j++) {
						espacio[i][j] = ((i == 1 && j < 2) || (i == 0 && j == 1)) ? true : false;
					}
				}
				espacio[0][2] = true;
				break;
			}

			// T
			case 5 : {
				for (int i = 0; i < 4; i++) {
					for (int j = 0; j < 4; j++) {
						espacio[i][j] = (i == 1 && j < 3) ? true : false;
					}
				}
				espacio[0][1] = true;
				break;
			}

			// Z
			case 6 : {
				for (int i = 0; i < 4; i++) {
					for (int j = 0; j < 4; j++) {
						espacio[i][j] = ((i == 0 && j < 2) || (i == 1 && j == 1)) ? true : false;
					}
				}
				espacio[1][3] = true;
				break;
			}

		}//Cierre del switch
	}//Cierre del método constructor

	public void girar() {

	}//Cierre del método

	public void drop() {
		this.fila--;
	}//Cierre del método

	/**
	* Método para obtener la fila de la Pieza
	* @return fila donde se encuentra la Pieza
	*/
	public int getFila() {
		return fila;
	}//Cierre del método

	/**
	* Método para obtener la columna de la Pieza
	* @return columna donde se encuentra la Pieza
	*/
	public int getColumna() {
		return columna;
	}//Cierre del método
}//Cierre de la clase
