package mx.unam.ciencias.edd;

import java.util.NoSuchElementException;
import java.lang.Math;

/**
 * <p>Clase abstracta para árboles binarios genéricos.</p>
 *
 * <p>La clase proporciona las operaciones básicas para árboles binarios, pero
 * deja la implementación de varias en manos de las subclases concretas.</p>
 */
public abstract class ArbolBinario<T> implements Coleccion<T> {

    /**
     * Clase interna protegida para vértices.
     */
    protected class Vertice implements VerticeArbolBinario<T> {

        /** El elemento del vértice. */
        public T elemento;
        /** El padre del vértice. */
        public Vertice padre;
        /** El izquierdo del vértice. */
        public Vertice izquierdo;
        /** El derecho del vértice. */
        public Vertice derecho;

        /**
         * Constructor único que recibe un elemento.
         * @param elemento el elemento del vértice.
         */
        public Vertice(T elemento) {
            // Aquí va su código.
			this.elemento = elemento;
        }

        /**
         * Nos dice si el vértice tiene un padre.
         * @return <code>true</code> si el vértice tiene padre,
         *         <code>false</code> en otro caso.
         */
        @Override public boolean hayPadre() {
            // Aquí va su código.
			return padre != null;
        }

        /**
         * Nos dice si el vértice tiene un izquierdo.
         * @return <code>true</code> si el vértice tiene izquierdo,
         *         <code>false</code> en otro caso.
         */
        @Override public boolean hayIzquierdo() {
            // Aquí va su código.
			return izquierdo != null;
        }

        /**
         * Nos dice si el vértice tiene un derecho.
         * @return <code>true</code> si el vértice tiene derecho,
         *         <code>false</code> en otro caso.
         */
        @Override public boolean hayDerecho() {
            // Aquí va su código.
			return derecho != null;
        }

        /**
         * Regresa el padre del vértice.
         * @return el padre del vértice.
         * @throws NoSuchElementException si el vértice no tiene padre.
         */
        @Override public VerticeArbolBinario<T> padre() {
            // Aquí va su código.
			if (padre == null)
				throw new NoSuchElementException("El vertice no tiene padre");
			return padre;
        }

        /**
         * Regresa el izquierdo del vértice.
         * @return el izquierdo del vértice.
         * @throws NoSuchElementException si el vértice no tiene izquierdo.
         */
        @Override public VerticeArbolBinario<T> izquierdo() {
            // Aquí va su código.
			if (izquierdo == null)
				throw new NoSuchElementException("El vertice no tiene izquierdo");
			return izquierdo;
        }

        /**
         * Regresa el derecho del vértice.
         * @return el derecho del vértice.
         * @throws NoSuchElementException si el vértice no tiene derecho.
         */
        @Override public VerticeArbolBinario<T> derecho() {
            // Aquí va su código.
			if (derecho == null)
				throw new NoSuchElementException("El vertice no tiene derecho");
			return derecho;
        }

        /**
         * Regresa la altura del vértice.
         * @return la altura del vértice.
         */
        @Override public int altura() {
            // Aquí va su código.
			return altura(this);
        }

		private int altura(Vertice v) {
			if (v == null)
				return -1;
			return 1 + Math.max(altura(v.izquierdo), altura(v.derecho));
		}
        /**
         * Regresa la profundidad del vértice.
         * @return la profundidad del vértice.
         */
        @Override public int profundidad() {
            // Aquí va su código.
			return profundidadAux(this);
        }

		private int profundidadAux(Vertice v) {
			if (v.padre == null)
				return 0;
			return 1 + profundidadAux(v.padre);
		}

        /**
         * Regresa el elemento al que apunta el vértice.
         * @return el elemento al que apunta el vértice.
         */
        @Override public T get() {
            // Aquí va su código.
			return elemento;
        }

        /**
         * Compara el vértice con otro objeto. La comparación es
         * <em>recursiva</em>. Las clases que extiendan {@link Vertice} deben
         * sobrecargar el método {@link Vertice#equals}.
         * @param objeto el objeto con el cual se comparará el vértice.
         * @return <code>true</code> si el objeto es instancia de la clase
         *         {@link Vertice}, su elemento es igual al elemento de éste
         *         vértice, y los descendientes de ambos son recursivamente
         *         iguales; <code>false</code> en otro caso.
         */
        @Override public boolean equals(Object objeto) {
            if (objeto == null || getClass() != objeto.getClass())
                return false;
            @SuppressWarnings("unchecked") Vertice vertice = (Vertice)objeto;
            // Aquí va su código.
			return equalsRecursivo(this, vertice);
		}

		/**
		 * Método recursivo que compara dos vertices y sus subarboles
		 * @param v1 El primer vertice
		 * @param v2 El segundo vertice
		 * @return <code>true</code> si su elementos son iguales y
         *        y los descendientes de ambos son recursivamente
		 *        <code>false</code> en otro caso.
		 */
		private boolean equalsRecursivo(Vertice v1, Vertice v2) {
			if ((v1 == null && v2 != null)  || (v2 == null && v1 != null))
                return false;
            if (v1 == null && v2 == null)
                return true;
            if(!v2.elemento.equals(v1.elemento))
                return false;
				/* Regresamos el equals del subarbol izquierdo y derecho de los vertices hasta llegar a los casos bases*/
			return equalsRecursivo(v1.izquierdo,v2.izquierdo) && equalsRecursivo(v1.derecho,v2.derecho);
		}

        /**
         * Regresa una representación en cadena del vértice.
         * @return una representación en cadena del vértice.
         */
        public String toString() {
            // Aquí va su código.
			return elemento.toString();
        }
    }//Cierre de la clase vértice

    /** La raíz del árbol. */
    protected Vertice raiz;
    /** El número de elementos */
    protected int elementos;

    /**
     * Constructor sin parámetros. Tenemos que definirlo para no perderlo.
     */
    public ArbolBinario() {}

    /**
     * Construye un árbol binario a partir de una colección. El árbol binario
     * tendrá los mismos elementos que la colección recibida.
     * @param coleccion la colección a partir de la cual creamos el árbol
     *        binario.
     */
    public ArbolBinario(Coleccion<T> coleccion) {
        // Aquí va su código.
		if (coleccion.esVacia()) {
			raiz = null;
			return;
		}
		for (T elemento : coleccion)
			agrega(elemento);
    }

    /**
     * Construye un nuevo vértice, usando una instancia de {@link Vertice}. Para
     * crear vértices se debe utilizar este método en lugar del operador
     * <code>new</code>, para que las clases herederas de ésta puedan
     * sobrecargarlo y permitir que cada estructura de árbol binario utilice
     * distintos tipos de vértices.
     * @param elemento el elemento dentro del vértice.
     * @return un nuevo vértice con el elemento recibido dentro del mismo.
     */
    protected Vertice nuevoVertice(T elemento) {
        // Aquí va su código.
		return new Vertice(elemento);
    }

    /**
     * Regresa la altura del árbol. La altura de un árbol es la altura de su
     * raíz.
     * @return la altura del árbol.
     */
    public int altura() {
        // Aquí va su código.
		if (raiz == null)
			return -1;
		return raiz.altura();
    }

    /**
     * Regresa el número de elementos que se han agregado al árbol.
     * @return el número de elementos en el árbol.
     */
    @Override public int getElementos() {
        // Aquí va su código.
		return elementos;
    }

    /**
     * Nos dice si un elemento está en el árbol binario.
     * @param elemento el elemento que queremos comprobar si está en el árbol.
     * @return <code>true</code> si el elemento está en el árbol;
     *         <code>false</code> en otro caso.
     */
    @Override public boolean contiene(T elemento) {
        // Aquí va su código.
		return contiene(raiz,elemento);
    }

	/**
	 * Método Auxiliar recursivo que compara elementos hasta encontrar el que buscamos
	 * @param elemento el elemento que queremos comprobar si está en el árbol.
	 * @param v el vertice donde se está buscando atualmente
     * @return <code>true</code> si el elemento está en el árbol;
     *         <code>false</code> en otro caso.
	 */
	private boolean contiene(Vertice v, T elemento){
		if (v == null)
			return false;
		if (v.elemento.equals(elemento))
			return true;
		return contiene(v.izquierdo, elemento) || contiene(v.derecho, elemento);
	}

    /**
     * Busca el vértice de un elemento en el árbol. Si no lo encuentra regresa
     * <code>null</code>.
     * @param elemento el elemento para buscar el vértice.
     * @return un vértice que contiene el elemento buscado si lo encuentra;
     *         <code>null</code> en otro caso.
     */
    public VerticeArbolBinario<T> busca(T elemento) {
        // Aquí va su código.
		return busca(raiz,elemento);
    }

	/**
	 * Método Auxiliar recursivo que compara elementos hasta encontrar el que buscamos
	 * @param elemento el elemento que queremos comprobar si está en el árbol.
	 * @param v el vertice donde se está buscando atualmente
     * @return El vértice que contiene el elemento
	 */
	private VerticeArbolBinario<T> busca(Vertice v, T elemento) {
		if (v == null)
			return null;
		if (v.elemento.equals(elemento))
			return v;
		VerticeArbolBinario<T> izquierdo = busca(v.izquierdo, elemento);
		VerticeArbolBinario<T> derecho = busca(v.derecho, elemento);
		return izquierdo != null ? izquierdo : derecho;
	}

    /**
     * Regresa el vértice que contiene la raíz del árbol.
     * @return el vértice que contiene la raíz del árbol.
     * @throws NoSuchElementException si el árbol es vacío.
     */
    public VerticeArbolBinario<T> raiz() {
        // Aquí va su código.
		if (raiz == null)
			throw new NoSuchElementException("El arbol es vacío");
		return raiz;
    }

    /**
     * Nos dice si el árbol es vacío.
     * @return <code>true</code> si el árbol es vacío, <code>false</code> en
     *         otro caso.
     */
    @Override public boolean esVacia() {
        // Aquí va su código.
		return raiz == null;
    }

    /**
     * Limpia el árbol de elementos, dejándolo vacío.
     */
    @Override public void limpia() {
        // Aquí va su código.
		raiz = null;
		elementos = 0;
    }

    /**
     * Compara el árbol con un objeto.
     * @param objeto el objeto con el que queremos comparar el árbol.
     * @return <code>true</code> si el objeto recibido es un árbol binario y los
     *         árboles son iguales; <code>false</code> en otro caso.
     */
    @Override public boolean equals(Object objeto) {
        if (objeto == null || getClass() != objeto.getClass())
            return false;
        @SuppressWarnings("unchecked")
            ArbolBinario<T> arbol = (ArbolBinario<T>)objeto;
        // Aquí va su código.
		if (elementos != arbol.getElementos())
			return false;
		if (arbol.raiz == null && raiz == null)
			return true;
		return raiz.equals(arbol.raiz);
    }

    /**
     * Regresa una representación en cadena del árbol.
     * @return una representación en cadena del árbol.
     */
    @Override public String toString() {
        // Aquí va su código.
		if (raiz == null)
			return "";
		int[] arregloBinario = new int[altura()+1];
		for (int i = 0; i < arregloBinario.length; i++)
			arregloBinario[i] = 0;
		return toString(raiz, 0, arregloBinario);
    }

	/**
	 * Método Auxiliar que dibuja los espacios o simbolos necesarios en cada línea de la cadena
	 * @param nivel El nivel en el que se está trabajando
	 * @param arregloBinario 1 representa una rama vertical y 0 representa un espacio
	 * @return Una cadena con los espacios necesarios
	 */
	private String dibujaEspacios(int nivel, int[] arregloBinario) {
		String sFinal = "";
		for (int i = 0; i <= nivel-1; i++)
			if (arregloBinario[i] == 1)
				sFinal += "│  ";
			else
				sFinal += "   ";
		return sFinal;
	}

	/**
	 * Método Auxiliar que determina cuando agregar una rama y cuando agregar espacios
	 * @param v Vertice cuyo elemento se concatenará a la cadena final
	 * @param nivel El nivel en el que se está trabajando
	 * @param arregloBinario 1 representa una rama vertical y 0 representa un espacio
	 * @return Una representación en cadena del vertice recibido con las ramas definidad por el arbol binario
	 */
	private String toString(Vertice v, int nivel, int[] arregloBinario) {
		String sFinal = v.toString() + "\n";
		arregloBinario[nivel] = 1;
		if (v.hayIzquierdo() && v.hayDerecho()) {
			sFinal += dibujaEspacios(nivel, arregloBinario);
			sFinal += "├─›";
			sFinal += toString(v.izquierdo, nivel+1, arregloBinario);
			sFinal += dibujaEspacios(nivel, arregloBinario);
			sFinal += "└─»";
			arregloBinario[nivel] = 0;
			sFinal += toString(v.derecho, nivel+1, arregloBinario);
		} else if (v.izquierdo != null) {
			sFinal += dibujaEspacios(nivel, arregloBinario);
			sFinal += "└─›";
			arregloBinario[nivel] = 0;
			sFinal += toString(v.izquierdo, nivel+1, arregloBinario);
		} else if (v.derecho != null) {
			sFinal += dibujaEspacios(nivel, arregloBinario);
			sFinal += "└─»";
			arregloBinario[nivel] = 0;
			sFinal += toString(v.derecho, nivel+1, arregloBinario);
		}
		return sFinal;
	}

    /**
     * Convierte el vértice (visto como instancia de {@link
     * VerticeArbolBinario}) en vértice (visto como instancia de {@link
     * Vertice}). Método auxiliar para hacer esta audición en un único lugar.
     * @param vertice el vértice de árbol binario que queremos como vértice.
     * @return el vértice recibido visto como vértice.
     * @throws ClassCastException si el vértice no es instancia de {@link
     *         Vertice}.
     */
    protected Vertice vertice(VerticeArbolBinario<T> vertice) {
        return (Vertice) vertice;
    }

	/***************************************Funciones Auxiliares********************************************/

	/**
	 * Método que nos indica si el hijo es derecho
	 * @param v El vertice a comparar
	 * @return true en caso de serlo, false en caso contrario
	 */
	protected boolean esDerecho(Vertice v) {
		//Comparamos con == puesto que deben ser la misma referencia
        if (v.padre.derecho == v)
            return true;
        else
			return false;
    }

	/**
	 * Método que nos indica si el hijo es izquierdo
	 * @param v El vertice a comparar
	 * @return true en caso de serlo, false en caso contrario
	 */
	protected boolean esIzquierdo(Vertice v) {
		//Comparamos con == puesto que deben ser la misma referencia
        if (v.padre.izquierdo == v)
            return true;
        else
			return false;
    }
}
