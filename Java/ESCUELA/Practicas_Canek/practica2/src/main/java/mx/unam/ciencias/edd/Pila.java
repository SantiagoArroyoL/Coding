package mx.unam.ciencias.edd;

/**
 * Clase para pilas genéricas.
 */
public class Pila<T> extends MeteSaca<T> {

    /**
     * Regresa una representación en cadena de la pila.
     * @return una representación en cadena de la pila.
     */
    @Override public String toString() {
        // Aquí va su código.
		// Aquí va su código.
		if (cabeza == null || rabo == null)
			return "";
		Nodo n = cabeza;
		String cadenaFinal = n.elemento + "\n";
		while (n != rabo) {
			n = n.siguiente;
			cadenaFinal += n.elemento + "\n";
		}
		return cadenaFinal;
    }

    /**
     * Agrega un elemento al tope de la pila.
     * @param elemento el elemento a agregar.
     * @throws IllegalArgumentException si <code>elemento</code> es
     *         <code>null</code>.
     */
    @Override public void mete(T elemento) {
        // Aquí va su código.
		if (elemento == null)
			throw new IllegalArgumentException("El elemento a meter es nulo!");
		Nodo nuevo = new Nodo(elemento);
		if (cabeza == null){
			cabeza = rabo = nuevo;
		} else {
			nuevo.siguiente = cabeza;
			cabeza = nuevo;
		}
    }
}
