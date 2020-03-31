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
                VerticeRojinegro vertice = (VerticeRojinegro)objeto;
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
		if (vertice.getClass() != this.raiz.getClass())
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
		VerticeRojinegro hijo, aux;
		VerticeRojinegro v = (VerticeRojinegro) busca(elemento);
		if (v == null)
			return;
		if (tieneDosHijos(v)) {
			aux = (VerticeRojinegro) maximoEnSubArbol(v.izquierdo);
			v.elemento = aux.elemento;
		    v = aux;
	    }
		if (noTieneHijos(v)) {
			v.izquierdo = nuevoVertice(null);
			v.izquierdo.padre = v;
 		}
		hijo = getHijo(v);
		eliminaVertice(v);
		if (esNegro(hijo) && esNegro(v)) {
			hijo.color = Color.NEGRO;
			rebalanceaEliminado(hijo);
		} else {
			hijo.color = Color.NEGRO;
		}
		eliminarFantasma(hijo);
    }

	/**
	* Auxiliar de Elimina. Elimina el posible vertice fantasma que pueda haber.
	* @param eliminar VerticeRojinegro que queremos ver si es fantasma
	**/
   private void eliminarFantasma(VerticeRojinegro v) {
	   if (v.elemento == null) {
		   eliminaHoja(v);
	   }
   }

	private boolean tieneDosHijos(Vertice v) {
		return v.derecho != null && v.izquierdo != null;
	}

	private void intercambia(VerticeRojinegro v1, VerticeRojinegro v2) {
		T p = v1.elemento;
		v1.elemento = v2.elemento;
		v2.elemento = p;
	}

	/**
     * Auxiliar de elimina. Elimina una hoja.
     * @param eliminar el elemento a eliminar que debe ser hoja.
     */
    private void eliminaHoja(Vertice eliminar) {
        if (this.raiz == eliminar) {
            this.raiz = null;
            this.ultimoAgregado = null;
        } else if (esIzquierdo(eliminar)) {
            eliminar.padre.izquierdo = null;
        } else {
            eliminar.padre.derecho = null;
        }
    }

	private boolean noTieneHijos(Vertice v) {
		return v.derecho == null && v.izquierdo == null;
	}

	private VerticeRojinegro getHijo(Vertice v) {
		if (v.hayDerecho())
			return (VerticeRojinegro) v.derecho;
		return (VerticeRojinegro) v.izquierdo;
	}

	private void rebalanceaEliminado(VerticeRojinegro v) {
		VerticeRojinegro hermano, padre, hIzquierdo, hDerecho;
		/* Caso 1 */
		if (!v.hayPadre()){
			this.raiz = v;
			return;
		}
		//Creamos al hermano
		padre = (VerticeRojinegro) v.padre;
		hermano = getHermano(v);
		/* Caso 2 */
		if (esRojo(hermano)) {
			padre.color = Color.ROJO;
			hermano.color = Color.NEGRO;
			if (esIzquierdo(v))
				super.giraIzquierda(padre);
			else
				super.giraDerecha(padre);
			padre = (VerticeRojinegro) v.padre;
			hermano = getHermano(v);
		}
		//Creamos a los sobrinos de v
		hIzquierdo = (VerticeRojinegro) hermano.izquierdo;
		hDerecho = (VerticeRojinegro) hermano.derecho;
		/* Caso 3, que siempre debe pasar despues del 2 */
		if((esNegro(padre) && esNegro(hermano)) && (esNegro(hIzquierdo) && esNegro(hDerecho))) {
			hermano.color = Color.ROJO;
			rebalanceaEliminado(padre);
			return;
		}
		/* Caso 4 */
		if((esRojo(padre) && esNegro(hermano)) && (esNegro(hIzquierdo) && esNegro(hDerecho))) {
			padre.color = Color.NEGRO;
			hermano.color = Color.ROJO;
			return;
		}
		/* Caso 5 */
		if ((esNegro(hIzquierdo) && esRojo(hDerecho)) && sobrinosCruzados(v,hIzquierdo,hDerecho)) {
			if (esNegro(hIzquierdo))
				hIzquierdo.color = Color.NEGRO;
			else
				hDerecho.color = Color.NEGRO;
			hermano.color = Color.ROJO;
			if (esIzquierdo(v)) {
				hIzquierdo.color = Color.NEGRO;
				super.giraDerecha(hermano);
			} else {
				hDerecho.color = Color.NEGRO;
				super.giraIzquierda(hermano);
			}
			hermano = getHermano(v);
			hIzquierdo = (VerticeRojinegro) hermano.izquierdo;
			hDerecho = (VerticeRojinegro) hermano.derecho;
		}
		/* Caso 6, que siempre debe ocurrir despues del 5 */
		hermano.color = padre.color;
		padre.color = Color.NEGRO;
		if (esIzquierdo(v)) {
			hDerecho.color = Color.NEGRO;
			super.giraIzquierda(padre);
		} else {
			hIzquierdo.color = Color.ROJO;
			super.giraDerecha(padre);
		}
	}

	private VerticeRojinegro getHermano(VerticeRojinegro v) {
		if (esIzquierdo(v))
			return (VerticeRojinegro) v.padre.derecho;
		else
			return (VerticeRojinegro) v.padre.izquierdo;
	}

	private boolean sobrinosCruzados(VerticeRojinegro v, VerticeRojinegro hIzquierdo, VerticeRojinegro hDerecho) {
		return (esNegro(hIzquierdo) && esDerecho(v)) || (esNegro(hDerecho) && esIzquierdo(v));
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

	/***************************************Funciones Auxiliares********************************************/

	private boolean esRojo(VerticeRojinegro vertice) {
		return vertice != null && vertice.color == Color.ROJO;
	}

	private boolean esNegro(VerticeRojinegro vertice) {
		return vertice.color == Color.NEGRO;
	}
}
