package mx.unam.ciencias.edd;

import java.lang.Math;

/**
 * <p>Clase para árboles AVL.</p>
 *
 * <p>Un árbol AVL cumple que para cada uno de sus vértices, la diferencia entre
 * la áltura de sus subárboles izquierdo y derecho está entre -1 y 1.</p>
 */
public class ArbolAVL<T extends Comparable<T>> extends ArbolBinarioOrdenado<T> {

    /**
     * Clase interna protegida para vértices.
     */
    protected class VerticeAVL extends Vertice {

        /** La altura del vértice. */
        public int altura;

        /**
         * Constructor único que recibe un elemento.
         * @param elemento el elemento del vértice.
         */
        public VerticeAVL(T elemento) {
            // Aquí va su código.
			super(elemento);
			altura = 0;
        }

        /**
         * Regresa la altura del vértice.
         * @return la altura del vértice.
         */
        @Override public int altura() {
            // Aquí va su código.
			return altura;
        }

        /**
         * Regresa una representación en cadena del vértice AVL.
         * @return una representación en cadena del vértice AVL.
         */
        @Override public String toString() {
            // Aquí va su código.
			return elemento.toString() + " " + altura + "/" + balance(this);
        }

        /**
         * Compara el vértice con otro objeto. La comparación es
         * <em>recursiva</em>.
         * @param objeto el objeto con el cual se comparará el vértice.
         * @return <code>true</code> si el objeto es instancia de la clase
         *         {@link VerticeAVL}, su elemento es igual al elemento de éste
         *         vértice, los descendientes de ambos son recursivamente
         *         iguales, y las alturas son iguales; <code>false</code> en
         *         otro caso.
         */
        @Override public boolean equals(Object objeto) {
            if (objeto == null || getClass() != objeto.getClass())
                return false;
            @SuppressWarnings("unchecked") VerticeAVL vertice = (VerticeAVL)objeto;
            // Aquí va su código.
			return altura == vertice.altura && super.equals(objeto);
        }
    }

    /**
     * Constructor sin parámetros. Para no perder el constructor sin parámetros
     * de {@link ArbolBinarioOrdenado}.
     */
    public ArbolAVL() { super(); }

    /**
     * Construye un árbol AVL a partir de una colección. El árbol AVL tiene los
     * mismos elementos que la colección recibida.
     * @param coleccion la colección a partir de la cual creamos el árbol AVL.
     */
    public ArbolAVL(Coleccion<T> coleccion) {
        super(coleccion);
    }

    /**
     * Construye un nuevo vértice, usando una instancia de {@link VerticeAVL}.
     * @param elemento el elemento dentro del vértice.
     * @return un nuevo vértice con el elemento recibido dentro del mismo.
     */
    @Override protected Vertice nuevoVertice(T elemento) {
        // Aquí va su código.
		return new VerticeAVL(elemento);
    }

    /**
     * Agrega un nuevo elemento al árbol. El método invoca al método {@link
     * ArbolBinarioOrdenado#agrega}, y después balancea el árbol girándolo como
     * sea necesario.
     * @param elemento el elemento a agregar.
     */
    @Override public void agrega(T elemento) {
        // Aquí va su código.
		super.agrega(elemento);
		rebalancea(ultimoAgregado.padre);
    }

    /**
     * Elimina un elemento del árbol. El método elimina el vértice que contiene
     * el elemento, y gira el árbol como sea necesario para rebalancearlo.
     * @param elemento el elemento a eliminar del árbol.
     */
    @Override public void elimina(T elemento) {
        // Aquí va su código.
		VerticeAVL v = (VerticeAVL) busca(elemento);
		if (v == null)
			return;
		elementos--;
		if (v.izquierdo != null && v.derecho != null)
            v = (VerticeAVL) intercambiaEliminable(v);
		eliminaVertice(v);
		rebalancea(v.padre);
    }

	/**
	 * Algoritmo auxiliar recursivo que rebalancea el arbol
	 * El método funciona para eliminar y agrega
	 * @param vertice El padre del vertice agregado o eliminado
	 */
	private void rebalancea(VerticeArbolBinario<T> vertice) {
		int balance;
		VerticeAVL p,q;
		if (vertice == null)
			return;
		VerticeAVL v = (VerticeAVL) vertice;
		v.altura = getAlturaCalculada(v);
		balance = balance(v);
		if (balance == -2) {
			q = (VerticeAVL) v.derecho;
			if (balance(q) == 1)
				giraDerechaAVL(q);
			giraIzquierdaAVL(v);
		} else if (balance == 2) {
			p = (VerticeAVL) v.izquierdo;
			if (balance(p) == -1)
				giraIzquierdaAVL(p);
			giraDerechaAVL(v);
		}
		rebalancea(v.padre);
	}

	/**
	 * Método que gira a la izquierda sobre unn vertice
	 * El método además actualiza las alturas del vertice y su padre
	 * @param vertice el vertice sobre el que giramos
	 */
	private void giraIzquierdaAVL(VerticeAVL vertice){
	    super.giraIzquierda(vertice);
	    vertice.altura = getAlturaCalculada(vertice);
		VerticeAVL padre = (VerticeAVL) vertice.padre;
		padre.altura = getAlturaCalculada(padre);
    }

	/**
	 * Método que gira a la derecha sobre unn vertice
	 * El método además actualiza las alturas del vertice y su padre
	 * @param vertice el vertice sobre el que giramos
	 */
    private void giraDerechaAVL(VerticeAVL vertice){
		super.giraDerecha(vertice);
	    vertice.altura = getAlturaCalculada(vertice);
		VerticeAVL padre = (VerticeAVL) vertice.padre;
		padre.altura = getAlturaCalculada(padre);
    }

    /**
     * Lanza la excepción {@link UnsupportedOperationException}: los árboles AVL
     * no pueden ser girados a la derecha por los usuarios de la clase, porque
     * se desbalancean.
     * @param vertice el vértice sobre el que se quiere girar.
     * @throws UnsupportedOperationException siempre.
     */
    @Override public void giraDerecha(VerticeArbolBinario<T> vertice) {
        throw new UnsupportedOperationException("Los árboles AVL no  pueden " +
                                                "girar a la izquierda por el " +
                                                "usuario.");
    }

    /**
     * Lanza la excepción {@link UnsupportedOperationException}: los árboles AVL
     * no pueden ser girados a la izquierda por los usuarios de la clase, porque
     * se desbalancean.
     * @param vertice el vértice sobre el que se quiere girar.
     * @throws UnsupportedOperationException siempre.
     */
    @Override public void giraIzquierda(VerticeArbolBinario<T> vertice) {
        throw new UnsupportedOperationException("Los árboles AVL no  pueden " +
                                                "girar a la derecha por el " +
                                                "usuario.");
    }

	/***************************************Funciones Auxiliares********************************************/

	/**
	 * Método auxiliar que nos regresa la altura de un vertice o -1 si este es nulo
	 * @param v el vertice a calcular
	 * @return el valor entero de la altura del vertice
	 */
	private int getAltura(VerticeArbolBinario<T> v) {
		VerticeAVL vertice = (VerticeAVL) v;
        return vertice == null ? -1 : vertice.altura;
    }

	/**
	 * Calcula la altura del vertice que es el máximo de la diferencia de sus dos subarboles 
	 * @param vertice el vertice a evaluar
	 * @return el valor entero de la altura calculada
	 */
    private int getAlturaCalculada(VerticeAVL vertice) {
        return 1 + Math.max(getAltura(vertice.izquierdo), getAltura(vertice.derecho));
    }

	/**
	 * Calcula el balance del vertice que es la diferencia de sus dos subarboles
	 * @param vertice el vertice a evaluar
	 * @return el valor entero de el balance del vertice
	 */
    private int balance(VerticeAVL vertice) {
        return getAltura(vertice.izquierdo) - getAltura(vertice.derecho);
    }
}
