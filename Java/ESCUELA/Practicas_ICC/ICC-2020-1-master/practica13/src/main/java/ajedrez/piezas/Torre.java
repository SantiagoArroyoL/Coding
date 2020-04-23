package ajedrez.piezas;
import ajedrez.Tablero;
import java.util.List;
import java.util.LinkedList;

/**
 * Clase Torre.
 *
 * @author Arroyo Lozano Santiago
 * @version 24/10/2019 A
 */
public class Torre extends Pieza{

	/**
	 * Constructor Torre.
	 *
	 * @param color El color de la Torre
	 * @param posicion La posicion de la Torre
	 */
	public Torre(Color color, Posicion posicion) {
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

		//For de las columnas
		for (int i = columna; i <= 7; i++) {
			Pieza p1 = tab.obtenerPieza(fila,i);
			for (int j = columna; j >= 0; j--) {
				Pieza p2 = tab.obtenerPieza(fila,j);
				if (p1 == null && columna + n <= 7) {
				// if (columna + n <= 7) {
					jugadas.add(new Posicion(fila, columna + n));
					n++;
				} if (p2 == null && columna - m >= 0) {
				} if (columna - m >= 0) {
						jugadas.add(new Posicion(fila, columna - m));
						m++;
				}  else if (p2.obtenerColor() != obtenerColor()) {
					jugadas.add(new Posicion(fila, columna - (m - 1)));
					break;
				}
			}
			if (p1.obtenerColor() != obtenerColor()) {
				jugadas.add(new Posicion(fila, columna + (n +1)));
				break;
			}
		}

		n = 1;
		m = 1;
		//For de las filas
		for (int i = fila; i <= 7; i++) {
			Pieza p1 = tab.obtenerPieza(i,i);
			for (int j = fila; j >= 0; j--) {
				Pieza p2 = tab.obtenerPieza(j,j);
				if (p1 == null && fila + n <= 7) {
				// if (fila + n <= 7) {
					jugadas.add(new Posicion(fila + n, columna));
					n++;
				}  if (p2 == null && fila - m >= 0) {
				// }  if (fila - m >= 0) {
						jugadas.add(new Posicion(fila - m , columna));
						m++;
				} else if (p2.obtenerColor() != obtenerColor()) {
					jugadas.add(new Posicion(fila - (m - 1), columna));
					break;
				}
			}
			if (p1.obtenerColor() != obtenerColor()) {
				jugadas.add(new Posicion(fila + (n +1), columna ));
				break;
			}
		}

		return jugadas;
	}
}
