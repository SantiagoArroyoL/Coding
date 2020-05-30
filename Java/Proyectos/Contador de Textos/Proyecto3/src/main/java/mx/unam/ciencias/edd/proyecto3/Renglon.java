package mx.unam.ciencias.edd.proyecto3;

import java.text.Collator;

/**
 * Clase encargada de simular el compartamiento de cada renglon recibido.
 * La clase tiene un atributo String cadena que es el valor en cadena de dicho renglon.
 * Sobreescribimos el método compareTo para poder comparar con los parámetros que queremos
 *
 * @author Arroyo Lozano Santiago
 * @version 2.0
 * @since 23/05/2020
 */
public class Renglon implements Comparable<Renglon> {

	/*Valor en cadena del renglón*/
	protected String cadena;

	/**
	 * Constructor que inicializa el atributo cadena
	 * @param cadena EL valor que tomará nuestro atributo
	 */
	public Renglon(String cadena) {
		this.cadena = cadena;
	}

	/**
	 * Método que regresa el valor en cadena del renglon
	 * @return E atributo cadena
	 */
	@Override public String toString() {
		return cadena;
	}

	/**
	 * Método que compara este renglón con otra instancia de la misma clase
	 * Para establecer un orden predeterminado como queremos usamos un Collator
	 * Este ignora los acentos y las mayusculas
	 * Basta con sólo reemplazar temporalmente los espacios, saltos de línea y tabulaciones
	 * para hacer todavía más imparcial la comparación
	 * @param r El otro renglón a comparar
	 * @return Valor entero. Si es mayor a cero entonces r es de menor orden. Si regresa cero entonces son iguales
	 * 		y si regresa un entero negativo es porque r es de mayor orden
	 */
	@Override public int compareTo(Renglon r) {
		Collator collator = Collator.getInstance();
		collator.setStrength(Collator.PRIMARY);
		String temp = reemplaza(cadena);
		String otra = reemplaza(r.cadena);
		return collator.compare(temp,otra);
	}

	/**
	 * Método auxiliar que elimina los espacios, saltos de línea y tabulaciones en la cadena recibida
	 * @param str La cadena a reemplazar
	 * @return Una copia de la cadena recibida ya reemplazada
	 */
	private String reemplaza(String str) {
		return str.replaceAll("\\P{L}+", "");
	}

}//Cierre de la clase Renglon
