package ajedrez.piezas;
import ajedrez.Tablero;
import java.util.List;
import java.util.LinkedList;

/**
 * Clase Alfil.
 *
 * @author Arroyo Lozano Santiago
 * @version 24/10/2019 A
 */
public class Alfil extends Pieza {

	/**
	 * Constructor Alfil.
	 *
	 * @param color El color del Alfil
	 * @param posicion La posicion del Alfil
	 */
	public Alfil(Color color, Posicion posicion) {
		super(color,posicion);
	}

	Tablero tab = Tablero.obtenerInstancia();

	/**
	 * Método para obtener Jugadas Legales
	 * @return una lista con todas las posiciones legales
	 */
	@Override
	public List<Posicion> obtenerJugadasLegales() {
		int n = 1;
		int m = 1;
		LinkedList<Posicion> jugadas = new LinkedList<>();
		int fila = obtenerPosicion().obtenerFila();
		int columna = obtenerPosicion().obtenerColumna();

		//For de las diagonales 1
		for (int i = fila; i <= 7; i++) {
			Pieza p1 = tab.obtenerPieza(i,i);
			for (int j = fila; j >= 0; j--) {
				Pieza p2 = tab.obtenerPieza(j,j);
				if ((p1 == null && fila + n <= 7 ) && columna - n >= 0) {
				// if (fila + n <= 7 && columna - n >= 0) {
					jugadas.add(new Posicion(fila + n, columna - n));
					n++;
				} if ((p2 == null && columna + m <= 7) && fila - m >= 0) {
				// } if (columna + m <= 7 && fila - m >= 0) {
						jugadas.add(new Posicion(fila -m , columna + m));
						m++;
				}  else if (p2.obtenerColor() != obtenerColor()) {
					jugadas.add(new Posicion(fila - (m - 1), columna + (m - 1)));
					break;
				}
			}
			if (p1.obtenerColor() != obtenerColor()) {
				jugadas.add(new Posicion(fila + (n + 1), columna - (n + 1) ));
				break;
			}
		}

		//For de las diagonales 2
		for (int i = fila; i <= 7; i++) {
			Pieza p1 = tab.obtenerPieza(i,columna);
			for (int j = fila; j >= 0; j--) {
				Pieza p2 = tab.obtenerPieza(j,columna);
				if ((p1 == null && columna + n <= 7) && fila + n <= 7) {
				// if (columna + n <= 7 && fila + n <= 7) {
					jugadas.add(new Posicion(fila + n, columna + n));
					n++;
				} if ((p2 == null && columna - m >= 0) && fila -n >= 0) {
				// } if (columna - m >= 0 && fila -n >= 0) {
						jugadas.add(new Posicion(fila - m , columna - m));
						m++;
				} else if (p2.obtenerColor() != obtenerColor()) {
					jugadas.add(new Posicion(fila - (m - 1), columna - (m - 1) ));
					break;
				}
			}
			if (p1.obtenerColor() != obtenerColor()) {
				jugadas.add(new Posicion(fila + (n + 1), columna + (n + 1) ));
				break;
			}
		}

		return jugadas;

	}
}
