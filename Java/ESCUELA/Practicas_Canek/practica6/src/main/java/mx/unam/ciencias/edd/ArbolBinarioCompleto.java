package mx.unam.ciencias.edd;

import java.lang.Math;
import java.util.Iterator;

/**
 * <p>Clase para árboles binarios completos.</p>
 *
 * <p>Un árbol binario completo agrega y elimina elementos de tal forma que el
 * árbol siempre es lo más cercano posible a estar lleno.</p>
 */
public class ArbolBinarioCompleto<T> extends ArbolBinario<T> {

    /* Clase interna privada para iteradores. */
    private class Iterador implements Iterator<T> {

        /* Cola para recorrer los vértices en BFS. */
        private Cola<Vertice> cola;

        /* Inicializa al iterador. */
        public Iterador() {
            // Aquí va su código.
			cola = new Cola<Vertice>();
			if (raiz != null)
				cola.mete(raiz);
        }

        /* Nos dice si hay un elemento siguiente. */
        @Override public boolean hasNext() {
            // Aquí va su código.
			return !cola.esVacia();
        }

        /* Regresa el siguiente elemento en orden BFS. */
        @Override public T next() {
            // Aquí va su código.
			Vertice temp = cola.saca();
			if (temp.hayIzquierdo())
				cola.mete(temp.izquierdo);
			if (temp.hayDerecho())
				cola.mete(temp.derecho);
			return temp.elemento;
        }
    }

    /**
     * Constructor sin parámetros. Para no perder el constructor sin parámetros
     * de {@link ArbolBinario}.
     */
    public ArbolBinarioCompleto() { super(); }

    /**
     * Construye un árbol binario completo a partir de una colección. El árbol
     * binario completo tiene los mismos elementos que la colección recibida.
     * @param coleccion la colección a partir de la cual creamos el árbol
     *        binario completo.
     */
    public ArbolBinarioCompleto(Coleccion<T> coleccion) {
        super(coleccion);
    }

    /**
     * Agrega un elemento al árbol binario completo. El nuevo elemento se coloca
     * a la derecha del último nivel, o a la izquierda de un nuevo nivel.
     * @param elemento el elemento a agregar al árbol.
     * @throws IllegalArgumentException si <code>elemento</code> es
     *         <code>null</code>.
     */
    @Override public void agrega(T elemento) {
		// Aquí va su código.
		if (elemento == null)
			throw new IllegalArgumentException("El elemento a agregar es null");
		Vertice v = nuevoVertice(elemento);
		elementos++;
		if (raiz == null) {
			raiz = v;
			return;
		}
		Vertice temp = bfsAgregador();
		if (!temp.hayIzquierdo()){
		 	temp.izquierdo = v;
			v.padre = temp;
		} else {
			temp.derecho = v;
			v.padre = temp;
		}
    }

    /**
     * Elimina un elemento del árbol. El elemento a eliminar cambia lugares con
     * el último elemento del árbol al recorrerlo por BFS, y entonces es
     * eliminado.
     * @param elemento el elemento a eliminar.
     */
    @Override public void elimina(T elemento) {
        // Aquí va su código.
		Vertice v = vertice(busca(elemento));
		if (v == null)
			return;
		elementos--;
		if (elementos == 0) {
			raiz = null;
			return;
		}
		/*Buscamos el último vértice por bfs*/
		Vertice ultimo = bfsAuxiliar();
		Vertice padre = ultimo.padre;
		T temp = ultimo.elemento;
		/*Intercambiamos los elementos*/
		ultimo.elemento = v.elemento;
		v.elemento = temp;
		/*Cambiamos al padre para desconectar a su hijo*/
		if (padre.derecho == ultimo)
		 	padre.derecho = null;
		else
			padre.izquierdo = null;
    }

    /**
     * Regresa la altura del árbol. La altura de un árbol binario completo
     * siempre es ⌊log<sub>2</sub><em>n</em>⌋.
     * @return la altura del árbol.
     */
    @Override public int altura() {
        // Aquí va su código.
		if (raiz == null)
			return -1;
		return log2(elementos);
    }

    /**
     * Realiza un recorrido BFS en el árbol, ejecutando la acción recibida en
     * cada elemento del árbol.
     * @param accion la acción a realizar en cada elemento del árbol.
     */
    public void bfs(AccionVerticeArbolBinario<T> accion) {
        // Aquí va su código.
		Cola<Vertice> cola = new Cola<Vertice>();
		cola.mete(raiz);
		while(!cola.esVacia()) {
			Vertice temp = cola.saca();
			accion.actua(temp);
			if (temp.hayIzquierdo())
				cola.mete(temp.izquierdo);
			if (temp.hayDerecho())
				cola.mete(temp.derecho);
		}
    }

    /**
     * Regresa un iterador para iterar el árbol. El árbol se itera en orden BFS.
     * @return un iterador para iterar el árbol.
     */
    @Override public Iterator<T> iterator() {
        return new Iterador();
    }

	/***************************************Funciones Auxiliares********************************************/

	/**
	 * Método auxiliar para calcular el piso de logaritmos de base 2
	 * @param x El número entero a calcular
	 * @return El piso del logaritmo base 2 del entero recibido
	 */
	public static int log2(int x) {
    	return (int) Math.floor((Math.log(x) / Math.log(2)));
	}

	/**
	 * Método auxiliar que recorre el arbol por bfs y regresa el último vértice
	 * @return Ultimo vertice al recorrer el arbol
	 */
	private Vertice bfsAuxiliar() {
		Vertice temp = raiz;
		Cola<Vertice> cola = new Cola<Vertice>();
		cola.mete(raiz);
		while(!cola.esVacia()) {
			temp = cola.saca();
			if (temp.hayIzquierdo())
				cola.mete(temp.izquierdo);
			if (temp.hayDerecho())
				cola.mete(temp.derecho);
		}
		return temp;
	}

	/**
	 * Método auxiliar que recorre el arbol por bfs y regresa el último vértice sin hij
	 * @return Ultimo vertice al recorrer el arbol
	 */
	private Vertice bfsAgregador() {
		Vertice temp = raiz;
		Cola<Vertice> cola = new Cola<Vertice>();
		cola.mete(raiz);
		while(!cola.esVacia()) {
			temp = cola.saca();
			if (temp.hayIzquierdo())
				cola.mete(temp.izquierdo);
			else
				return temp;
			if (temp.hayDerecho())
				cola.mete(temp.derecho);
			else
				return temp;
		}
		return temp;
	}

	/**
	 * Método auxiliar que nos da la coordenada x de un vertice dado
	 * @param v El vertice a encontrar
	 * @return El valor dentero de la coordenada en x
	 */
	private int coordenadaX(Vertice v) {
		if (v == raiz)
			return 0;
		if (esIzquierdo(v))
			return 2*coordenadaX(v.padre);
		else
			return 2*coordenadaX(v.padre)+1;
	}
}
