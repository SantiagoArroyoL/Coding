/**
 * Clase que maneja los puntos y nos permite serializarlos
 * @author Arroyo Lozano Santiago
 * @version 18/10/2019 A
 */
package tetris;

import java.io.Serializable;

public class Puntos implements Serializable{
	private Integer marcador;
	private static final Puntos INSTANCIA = new Puntos();

	public Puntos(){
		marcador = new Integer(0);
	} 

	public static Puntos obtenerInstancia() {
        return INSTANCIA;
    }

	public void sumar(int n) {
		marcador += n;
	}

	public Integer getMarcador() {
		return marcador;
	}
}
