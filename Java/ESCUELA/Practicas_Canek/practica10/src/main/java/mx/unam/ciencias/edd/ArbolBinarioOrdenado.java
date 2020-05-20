package mx.unam.ciencias.edd;

import java.util.Iterator;

/**
 * <p>Clase para árboles binarios ordenados. Los árboles son genéricos, pero
 * acotados a la interfaz {@link Comparable}.</p>
 *
 * <p>Un árbol instancia de esta clase siempre cumple que:</p>
 * <ul>
 *   <li>Cualquier elemento en el árbol es mayor o igual que todos sus
 *       descendientes por la izquierda.</li>
 *   <li>Cualquier elemento en el árbol es menor o igual que todos sus
 *       descendientes por la derecha.</li>
 * </ul>
 */
public class ArbolBinarioOrdenado<T extends Comparable<T>> extends ArbolBinario<T> {

    /* Clase interna privada para iteradores. */
    private class Iterador implements Iterator<T> {

        /* Pila para recorrer los vértices en DFS in-order. */
        private Pila<Vertice> pila;

        /* Inicializa al iterador. */
        public Iterador() {
            // Aquí va su código.
			pila = new Pila<Vertice>();
            Vertice v = raiz;
            while (v != null) {
                pila.mete(v);
                v = v.izquierdo;
            }
        }

        /* Nos dice si hay un elemento siguiente. */
        @Override public boolean hasNext() {
            // Aquí va su código.
   			return !pila.esVacia();
        }

        /* Regresa el siguiente elemento en orden DFS in-order. */
        @Override public T next() {
            // Aquí va su código.
			Vertice v = pila.saca();
			T temp = v.elemento;
			if (v.hayDerecho()) {
				v = v.derecho;
				while (v.hayIzquierdo()) {
					pila.mete(v);
					v = v.izquierdo;
				}
				pila.mete(v);
			}
			return temp;
        }
    }

    /**
     * El vértice del último elemento agegado. Este vértice sólo se puede
     * garantizar que existe <em>inmediatamente</em> después de haber agregado
     * un elemento al árbol. Si cualquier operación distinta a agregar sobre el
     * árbol se ejecuta después de haber agregado un elemento, el estado de esta
     * variable es indefinido.
     */
    protected Vertice ultimoAgregado;

    /**
     * Constructor sin parámetros. Para no perder el constructor sin parámetros
     * de {@link ArbolBinario}.
     */
    public ArbolBinarioOrdenado() { super(); }

    /**
     * Construye un árbol binario ordenado a partir de una colección. El árbol
     * binario ordenado tiene los mismos elementos que la colección recibida.
     * @param coleccion la colección a partir de la cual creamos el árbol
     *        binario ordenado.
     */
    public ArbolBinarioOrdenado(Coleccion<T> coleccion) {
        super(coleccion);
    }

    /**
     * Agrega un nuevo elemento al árbol. El árbol conserva su orden in-order.
     * @param elemento el elemento a agregar.
	 * @throws IllegalArgumentException si <code>elemento</code> es
     *         <code>null</code>.
     */
    @Override public void agrega(T elemento) {
		if (elemento == null)
			throw new IllegalArgumentException("El elemento a agregar es null");
        // Aquí va su código.
		Vertice v = nuevoVertice(elemento);
		elementos++;
		if (raiz == null)
			raiz = v;
		else
			agregaAux(raiz,v);
		ultimoAgregado = v;
    }

	/**
	 * Método Auxiliar REcursivo que compara cada elemento del arbol
	 * para así agregar el nuevo vértice ene l lugar correspondiente
	 * @param actual El vertice actual que se está comparando con el nuevo
	 * @param nuevo El nuevo vertice que será comparado con todo el subarbol de actual
	 */
	private void agregaAux(Vertice actual, Vertice nuevo) {
		if (actual.elemento.compareTo(nuevo.elemento) >= 0)
			if (actual.izquierdo == null) {
				actual.izquierdo = nuevo;
				nuevo.padre = actual;
			}
			else
				agregaAux(actual.izquierdo, nuevo);
		else
			if (actual.derecho ==  null) {
				actual.derecho = nuevo;
				nuevo.padre = actual;
			}
			else
				agregaAux(actual.derecho, nuevo);
	}

    /**
     * Elimina un elemento. Si el elemento no está en el árbol, no hace nada; si
     * está varias veces, elimina el primero que encuentre (in-order). El árbol
     * conserva su orden in-order.
     * @param elemento el elemento a eliminar.
     */
    @Override public void elimina(T elemento) {
        // Aquí va su código.
		Vertice v = vertice(busca(elemento));
        if (v == null)
          return;
        if (v.hayIzquierdo() && v.hayDerecho())
          v = intercambiaEliminable(v);
        eliminaVertice(v);
        elementos--;
    }

    /**
     * Intercambia el elemento de un vértice con dos hijos distintos de
     * <code>null</code> con el elemento de un descendiente que tenga a lo más
     * un hijo.
     * @param vertice un vértice con dos hijos distintos de <code>null</code>.
     * @return el vértice descendiente con el que vértice recibido se
     *         intercambió. El vértice regresado tiene a lo más un hijo distinto
     *         de <code>null</code>.
     */
    protected Vertice intercambiaEliminable(Vertice vertice) {
        // Aquí va su código.
		Vertice v = maximoEnSubArbol(vertice.izquierdo);
        T temp = v.elemento;
        v.elemento = vertice.elemento;
        vertice.elemento = temp;
        return v;
    }

    /**
     * Elimina un vértice que a lo más tiene un hijo distinto de
     * <code>null</code> subiendo ese hijo (si existe).
     * @param vertice el vértice a eliminar; debe tener a lo más un hijo
     *                distinto de <code>null</code>.
     */
    protected void eliminaVertice(Vertice vertice) {
        // Aquí va su código.
		/*Dividimos en los 3 casos principales y además cada caso lo dividimos cuando hay padre y cuando no
		  El primero siendo que el vertice no tiene ningún hijo*/
		if (!vertice.hayIzquierdo() && !vertice.hayDerecho())
        	if (vertice.hayPadre())
            	if (vertice.padre.hayIzquierdo() && vertice.padre.izquierdo == vertice)
            		vertice.padre.izquierdo = null;
            	else
                	vertice.padre.derecho = null;
        	else
            	raiz = null;
		/*Segundo caso cuando el hijo es el derecho*/
        else if (!vertice.hayDerecho()) {
        	vertice.izquierdo.padre = vertice.padre;
          	if (vertice.hayPadre())
            	if (esIzquierdo(vertice))
              		vertice.padre.izquierdo = vertice.izquierdo;
            	else
              		vertice.padre.derecho = vertice.izquierdo;
          	else
	            raiz = vertice.izquierdo;
		/*Último caso cuando el hijo es el izquierdo*/
        } else {
        	vertice.derecho.padre = vertice.padre;
          	if (vertice.hayPadre())
            	if (esIzquierdo(vertice))
              		vertice.padre.izquierdo = vertice.derecho;
            	else
              		vertice.padre.derecho = vertice.derecho;
          	else
            	raiz = vertice.derecho;
        }
    }

    /**
     * Busca un elemento en el árbol recorriéndolo in-order. Si lo encuentra,
     * regresa el vértice que lo contiene; si no, regresa <code>null</code>.
     * @param elemento el elemento a buscar.
     * @return un vértice que contiene al elemento buscado si lo
     *         encuentra; <code>null</code> en otro caso.
     */
    @Override public VerticeArbolBinario<T> busca(T elemento) {
        // Aquí va su código.
		return buscaOrdenado(raiz, nuevoVertice(elemento));
    }

	private VerticeArbolBinario<T> buscaOrdenado(Vertice actual, Vertice nuevo) {
		if (actual == null)
			return null;
		if (actual.elemento.compareTo(nuevo.elemento) == 0)
			return actual;
		if (actual.elemento.compareTo(nuevo.elemento) > 0)
			return buscaOrdenado(actual.izquierdo, nuevo);
		return buscaOrdenado(actual.derecho, nuevo);
	}

    /**
     * Regresa el vértice que contiene el último elemento agregado al
     * árbol. Este método sólo se puede garantizar que funcione
     * <em>inmediatamente</em> después de haber invocado al método {@link
     * agrega}. Si cualquier operación distinta a agregar sobre el árbol se
     * ejecuta después de haber agregado un elemento, el comportamiento de este
     * método es indefinido.
     * @return el vértice que contiene el último elemento agregado al árbol, si
     *         el método es invocado inmediatamente después de agregar un
     *         elemento al árbol.
     */
    public VerticeArbolBinario<T> getUltimoVerticeAgregado() {
        // Aquí va su código.
		return ultimoAgregado;
    }

    /**
     * Gira el árbol a la derecha sobre el vértice recibido. Si el vértice no
     * tiene hijo izquierdo, el método no hace nada.
     * @param vertice el vértice sobre el que vamos a girar.
     */
    public void giraDerecha(VerticeArbolBinario<T> vertice) {
        // Aquí va su código.
		Vertice v = vertice(vertice);
        if (!v.hayIzquierdo())
            return;
        Vertice verticeIzquierdo = v.izquierdo;
        Vertice derechoIzquierdo = verticeIzquierdo.derecho;
        verticeIzquierdo.derecho = v;
        verticeIzquierdo.padre = v.padre;
        v.izquierdo = derechoIzquierdo;
        if (v.hayIzquierdo())
            v.izquierdo.padre = v;
        if (!verticeIzquierdo.hayPadre()) {
            raiz = verticeIzquierdo;
            v.padre = verticeIzquierdo;
        } else if (esDerecho(v))
            v.padre.derecho = verticeIzquierdo;
        else
			v.padre.izquierdo = verticeIzquierdo;
	    v.padre = verticeIzquierdo;
    }

    /**
     * Gira el árbol a la izquierda sobre el vértice recibido. Si el vértice no
     * tiene hijo derecho, el método no hace nada.
     * @param vertice el vértice sobre el que vamos a girar.
     */
    public void giraIzquierda(VerticeArbolBinario<T> vertice) {
        // Aquí va su código.
		Vertice v =  vertice(vertice);
        if (!v.hayDerecho())
            return;
        Vertice verticeDerecho = v.derecho;
        Vertice izquierdoDerecho = verticeDerecho.izquierdo;
        v.derecho = izquierdoDerecho;
        verticeDerecho.izquierdo = v;
        verticeDerecho.padre = v.padre;
        if (v.hayDerecho())
            v.derecho.padre = v;
        if (!verticeDerecho.hayPadre()) {
            raiz = verticeDerecho;
            v.padre = verticeDerecho;
        } else if (esDerecho(v))
            v.padre.derecho = verticeDerecho;
        else
			v.padre.izquierdo = verticeDerecho;
        v.padre = verticeDerecho;
    }

    /**
     * Realiza un recorrido DFS <em>pre-order</em> en el árbol, ejecutando la
     * acción recibida en cada elemento del árbol.
     * @param accion la acción a realizar en cada elemento del árbol.
     */
    public void dfsPreOrder(AccionVerticeArbolBinario<T> accion) {
        // Aquí va su código.
		dfsPreOrderAux(accion, raiz);
    }

	private void dfsPreOrderAux(AccionVerticeArbolBinario<T> accion, Vertice v) {
		if (v == null)
			return;
		accion.actua(v);
		dfsPreOrderAux(accion, v.izquierdo);
		dfsPreOrderAux(accion, v.derecho);
	}

    /**
     * Realiza un recorrido DFS <em>in-order</em> en el árbol, ejecutando la
     * acción recibida en cada elemento del árbol.
     * @param accion la acción a realizar en cada elemento del árbol.
     */
    public void dfsInOrder(AccionVerticeArbolBinario<T> accion) {
        // Aquí va su código.
		dfsInOrderAux(accion, raiz);
    }

	private void dfsInOrderAux(AccionVerticeArbolBinario<T> accion, Vertice v) {
		if (v == null)
			return;
		dfsInOrderAux(accion, v.izquierdo);
		accion.actua(v);
		dfsInOrderAux(accion, v.derecho);
	}

    /**
     * Realiza un recorrido DFS <em>post-order</em> en el árbol, ejecutando la
     * acción recibida en cada elemento del árbol.
     * @param accion la acción a realizar en cada elemento del árbol.
     */
    public void dfsPostOrder(AccionVerticeArbolBinario<T> accion) {
        // Aquí va su código.
		dfsPostOrderAux(accion, raiz);
    }

	private void dfsPostOrderAux(AccionVerticeArbolBinario<T> accion, Vertice v) {
		if (v == null)
			return;
		dfsPostOrderAux(accion, v.izquierdo);
		dfsPostOrderAux(accion, v.derecho);
		accion.actua(v);
	}

    /**
     * Regresa un iterador para iterar el árbol. El árbol se itera en orden.
     * @return un iterador para iterar el árbol.
     */
    @Override public Iterator<T> iterator() {
        return new Iterador();
    }

	/***************************************Funciones Auxiliares********************************************/

	/**
	 * Método que nos regresa un elemento que es mayor o igual que todos los elementos del subarbol
	 * definido por el vertice que se recibe como parametro
	 * @param v El vertice que define el subarbol
	 * @return El vertice que contine el maximal del subarbol
	 */
	protected Vertice maximoEnSubArbol(Vertice v) {
		if (v.derecho == null)
			return v;
		return maximoEnSubArbol(v.derecho);
	}

}
