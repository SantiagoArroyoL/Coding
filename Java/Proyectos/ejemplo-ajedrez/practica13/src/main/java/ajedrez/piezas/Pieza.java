package ajedrez.piezas;
import java.util.List;

/**
 * Clase abstracta pieza.
 *
 * @author Arroyo Lozano Santiago
 * @version 22/10/2019 A
 */
public abstract class Pieza {
	private Color color;
	private Posicion posicion;

	/**
	 * Constructor Pieza
	 *
	 * @param color El color de la pieza
	 * @param posicion La posicion de la pieza
	 */
	public Pieza(Color color, Posicion posicion) {
		this.color = color;
		this.posicion = posicion;
	}

	public abstract List<Posicion> obtenerJugadasLegales();

	/**
	 * Método getter del color
	 * @return El color de la pieza
	 */
	public Color obtenerColor() {
		return color;
	}

	/**
	 * Método getter de la posicion
	 * @return La posición de la pieza
	 */
	public Posicion obtenerPosicion() {
		return posicion;
	}

	/**
	 * Método setter de la posición
	 * @param posicion La posicion a asignar
	 */
	public void asignarPosicion(Posicion posicion) {
		this.posicion = posicion;
	}

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
		Pieza otra = (Pieza) obj;
		return color == otra.color && posicion.equals(otra.obtenerPosicion());
	}
}
