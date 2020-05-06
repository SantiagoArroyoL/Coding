package mx.unam.ciencias.edd;

/**
 * Clase para árboles rojinegros. Un árbol rojinegro cumple las siguientes
 * propiedades:
 *
 * <ol>
 *  <li>Todos los vértices son NEGROS o ROJOS.</li>
 *  <li>La raíz es NEGRA.</li>
 *  <li>Todas las hojas (<code>null</code>) son NEGRAS (al igual que la raíz).</li>
 *  <li>Un vértice ROJO siempre tiene dos hijos NEGROS.</li>
 *  <li>Todo camino de un vértice a alguna de sus hojas descendientes tiene el
 *      mismo número de vértices NEGROS.</li>
 * </ol>
 *
 * Los árboles rojinegros se autobalancean.
 */
public class ArbolRojinegro<T extends Comparable<T>> extends ArbolBinarioOrdenado<T> {

    /**
     * Clase interna protegida para vértices.
     */
    protected class VerticeRojinegro extends Vertice {

        /** El color del vértice. */
        public Color color;

        /**
         * Constructor único que recibe un elemento.
         * @param elemento el elemento del vértice.
         */
        public VerticeRojinegro(T elemento) {
            // Aquí va su código.
			super(elemento);
			color = Color.NINGUNO;
        }

        /**
         * Regresa una representación en cadena del vértice rojinegro.
         * @return una representación en cadena del vértice rojinegro.
         */
        public String toString() {
            // Aquí va su código.
			if (color == Color.ROJO)
				return "R{" + elemento.toString() + "}";
			if (color == Color.NEGRO)
				return "N{" + elemento.toString() + "}";
			return "";
        }

        /**
         * Compara el vértice con otro objeto. La comparación es
         * <em>recursiva</em>.
         * @param objeto el objeto con el cual se comparará el vértice.
         * @return <code>true</code> si el objeto es instancia de la clase
         *         {@link VerticeRojinegro}, su elemento es igual al elemento de
         *         éste vértice, los descendientes de ambos son recursivamente
         *         iguales, y los colores son iguales; <code>false</code> en
         *         otro caso.
         */
        @Override public boolean equals(Object objeto) {
            if (objeto == null || getClass() != objeto.getClass())
                return false;
            @SuppressWarnings("unchecked")
                VerticeRojinegro vertice = (VerticeRojinegro) objeto;
            // Aquí va su código.
			return color == vertice.color && super.equals(vertice);
        }
    }

    /**
     * Constructor sin parámetros. Para no perder el constructor sin parámetros
     * de {@link ArbolBinarioOrdenado}.
     */
    public ArbolRojinegro() { super(); }

    /**
     * Construye un árbol rojinegro a partir de una colección. El árbol
     * rojinegro tiene los mismos elementos que la colección recibida.
     * @param coleccion la colección a partir de la cual creamos el árbol
     *        rojinegro.
     */
    public ArbolRojinegro(Coleccion<T> coleccion) {
        super(coleccion);
    }

    /**
     * Construye un nuevo vértice, usando una instancia de {@link
     * VerticeRojinegro}.
     * @param elemento el elemento dentro del vértice.
     * @return un nuevo vértice rojinegro con el elemento recibido dentro del mismo.
     */
    @Override protected VerticeRojinegro nuevoVertice(T elemento) {
        // Aquí va su código.
		return new VerticeRojinegro(elemento);
    }

    /**
     * Regresa el color del vértice rojinegro.
     * @param vertice el vértice del que queremos el color.
     * @return el color del vértice rojinegro.
     * @throws ClassCastException si el vértice no es instancia de {@link
     *         VerticeRojinegro}.
     */
    public Color getColor(VerticeArbolBinario<T> vertice) {
        // Aquí va su código.
		/* Esto para que incluso un arbol vacío pueda usar el método */
		if (vertice.getClass() != VerticeRojinegro.class)
			throw new ClassCastException("El vertice no es instancia de VerticeRojinegro!");
		VerticeRojinegro v = (VerticeRojinegro) vertice;
		return v.color;
    }

    /**
     * Agrega un nuevo elemento al árbol. El método invoca al método {@link
     * ArbolBinarioOrdenado#agrega}, y después balancea el árbol recoloreando
     * vértices y girando el árbol como sea necesario.
     * @param elemento el elemento a agregar.
     */
    @Override public void agrega(T elemento) {
        // Aquí va su código.
		super.agrega(elemento);
		VerticeRojinegro agregado = (VerticeRojinegro) ultimoAgregado;
		agregado.color = Color.ROJO;
		rebalancea(agregado);
    }

	/**
	 * Algoritmo auxiliar que rebalancea todo el arbol
	 * @param v el vertice sobre el que se hace el rebalanceo
	 */
	private void rebalancea(VerticeRojinegro v) {
		VerticeRojinegro tio, padre, abuelo;
		/* Caso1 */
		if (!v.hayPadre()) {
			v.color = Color.NEGRO;
			return;
		}
		padre = (VerticeRojinegro) v.padre;
		/* Caso 2 */
		if (esNegro(padre))
			return;
		// Procedemos a nombrar al tio y abuelo de v para los siguientes casos
		abuelo = (VerticeRojinegro) padre.padre;
		if (esIzquierdo(padre))
			tio = (VerticeRojinegro) abuelo.derecho;
		else
			tio = (VerticeRojinegro) abuelo.izquierdo;
		/* Caso 3 */
		if (esRojo(tio)) {
			padre.color = tio.color = Color.NEGRO;
			abuelo.color = Color.ROJO;
			rebalancea(abuelo);
			return;
		}
		/* Caso 4 */
		if (estanCruzados(v,padre)) {
			if (esIzquierdo(padre))
				super.giraIzquierda(padre);
			else
				super.giraDerecha(padre);
			VerticeRojinegro temp = v;
			v = padre;
			padre = temp;
		}
		/* Aquí comienza el Caso 5, que se debe ejecutar despues del Caso 4 siempre */
		padre.color = Color.NEGRO;
		abuelo.color = Color.ROJO;
		if (esIzquierdo(v))
			super.giraDerecha(abuelo);
		else
			super.giraIzquierda(abuelo);
	}

	/**
	 * Método auxiliar que nos dice si dos vertices están cruzados o no
	  * @param v Un vertice a evaluar
	  * @param p el otro vertice
	  * @return true si están cruzados - false en caso contrario
	  */
	private boolean estanCruzados(Vertice v, Vertice p) {
		return (esDerecho(p) && esIzquierdo(v)) || (esIzquierdo(p) && esDerecho(v));
	}

    /**
     * Elimina un elemento del árbol. El método elimina el vértice que contiene
     * el elemento, y recolorea y gira el árbol como sea necesario para
     * rebalancearlo.
     * @param elemento el elemento a eliminar del árbol.
     */
    @Override public void elimina(T elemento) {
        // Aquí va su código.
		VerticeRojinegro v = (VerticeRojinegro) super.busca(elemento);
        if (v == null)
            return;
        elementos--;
        if (v.izquierdo != null && v.derecho != null)
            v = (VerticeRojinegro) intercambiaEliminable(v);
        VerticeRojinegro fantasma = null;
        if (v.izquierdo == null && v.derecho == null) {
            fantasma = (VerticeRojinegro) nuevoVertice(null);
            fantasma.color = Color.NEGRO;
            fantasma.padre = v;
            v.izquierdo = fantasma;
        }
        VerticeRojinegro h = (VerticeRojinegro)hijo(v);
        eliminaVertice(v);
        if (esRojo(h)) {
            h.color = Color.NEGRO;
            return;
        }
        if (esNegro(v) && esNegro(h))
            elimina(h);
        if (fantasma != null)
            eliminaVertice(fantasma);
    }

	/**
	 * Método que desconecta a un vértice de todo el arbol
	 * @param v El vertice a desconectar
	 */
	private void elimina(VerticeRojinegro v) {
        if (v.padre == null)
            return;
        VerticeRojinegro padre = (VerticeRojinegro) v.padre;
        VerticeRojinegro hermano = (VerticeRojinegro) hermano(v);
        if (esRojo(hermano)) {
            padre.color = Color.ROJO;
            hermano.color = Color.NEGRO;
            if (esIzquierdo(v)){
                super.giraIzquierda(padre);
                hermano = (VerticeRojinegro) padre.derecho;
            }else{
                super.giraDerecha(padre);
                hermano = (VerticeRojinegro) padre.izquierdo;
            }
        }
        VerticeRojinegro hIzq = (VerticeRojinegro) hermano.izquierdo;
        VerticeRojinegro hDer = (VerticeRojinegro) hermano.derecho;
        if (esNegro(padre) && esNegro(hermano) && esNegro(hIzq) && esNegro(hDer)) {
            hermano.color = Color.ROJO;
            elimina(padre);
            return;
        } if (esRojo(padre) && esNegro(hermano) && esNegro(hIzq) && esNegro(hDer)) {
            hermano.color = Color.ROJO;
            padre.color = Color.NEGRO;
            return;
        } if ((esIzquierdo(v) && esRojo(hIzq) && esNegro(hDer)) ||
        (esDerecho(v) && esNegro(hIzq) && esRojo(hDer))) {
            hermano.color = Color.ROJO;
            if (esRojo(hIzq))
                hIzq.color = Color.NEGRO;
            else
                hDer.color = Color.NEGRO;
            if (esIzquierdo(v)) {
                super.giraDerecha(hermano);
                hermano = (VerticeRojinegro) padre.derecho;
            } else {
                super.giraIzquierda(hermano);
                hermano = (VerticeRojinegro) padre.izquierdo;
            }
        }
        hIzq = (VerticeRojinegro) hermano.izquierdo;
        hDer = (VerticeRojinegro) hermano.derecho;
        hermano.color = padre.color;
        padre.color = Color.NEGRO;
        if (esIzquierdo(v)) {
            hDer.color = Color.NEGRO;
            super.giraIzquierda(padre);
        } else {
            hIzq.color = Color.NEGRO;
            super.giraDerecha(padre);
        }
    }

    /**
     * Lanza la excepción {@link UnsupportedOperationException}: los árboles
     * rojinegros no pueden ser girados a la izquierda por los usuarios de la
     * clase, porque se desbalancean.
     * @param vertice el vértice sobre el que se quiere girar.
     * @throws UnsupportedOperationException siempre.
     */
    @Override public void giraIzquierda(VerticeArbolBinario<T> vertice) {
        throw new UnsupportedOperationException("Los árboles rojinegros no " +
                                                "pueden girar a la izquierda " +
                                                "por el usuario.");
    }

    /**
     * Lanza la excepción {@link UnsupportedOperationException}: los árboles
     * rojinegros no pueden ser girados a la derecha por los usuarios de la
     * clase, porque se desbalancean.
     * @param vertice el vértice sobre el que se quiere girar.
     * @throws UnsupportedOperationException siempre.
     */
    @Override public void giraDerecha(VerticeArbolBinario<T> vertice) {
        throw new UnsupportedOperationException("Los árboles rojinegros no " +
                                                "pueden girar a la derecha " +
                                                "por el usuario.");
    }

	/***************************************FuncionesAuxiliares********************************************/

	/**
     * Método auxiliar que nos dice si el color del vértice es negro.
     * @param vertice el vértice al que preguntaremos si su color es negro.
     * @return <code>true</code> si el color del vértice es negro;
     * <code>false</code> en otro caso.
     */
    private boolean esNegro(VerticeRojinegro vertice) {
      return (vertice == null || vertice.color == Color.NEGRO);
    }

    /**
     * Método auxiliar que nos dice si el color del vértice es rojos.
     * @param vertice el vértice al que preguntaremos si su color es rojo.
     * @return <code>true</code> si el color del vértice es rojo;
     * <code>false</code> en otro caso.
     */
    private boolean esRojo(VerticeRojinegro vertice) {
      return (vertice != null && vertice.color == Color.ROJO);
    }

	/**
     * Método auxiliar que nos regresa el vértice hermano.
     * @param vertice el vértice del que obtendremos el hermano.
     * @return el hermano del vértice.
     */
    private VerticeArbolBinario<T> hermano(Vertice vertice) {
      Vertice p = vertice.padre;
      if (vertice == p.izquierdo)
      return p.derecho;
      return p.izquierdo;
    }

    /**
     * Método auxiliar que nos regresa el vértice hijo.
     * @param vertice el vértice del que obtendremos el hijo.
     * @return el hijo del vértice.
     */
    private VerticeArbolBinario<T> hijo(Vertice vertice) {
      if (vertice.izquierdo == null)
        return vertice.derecho;
      return vertice.izquierdo;
    }
}
