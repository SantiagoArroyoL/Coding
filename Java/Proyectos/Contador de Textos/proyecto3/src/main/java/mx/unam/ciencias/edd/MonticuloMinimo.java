package mx.unam.ciencias.edd;

import java.lang.Math;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Clase para montículos mínimos (<i>min heaps</i>).
 */
public class MonticuloMinimo<T extends ComparableIndexable<T>> implements Coleccion<T>, MonticuloDijkstra<T> {

    /* Clase interna privada para iteradores. */
    private class Iterador implements Iterator<T> {

        /* Índice del iterador. */
        private int indice;

        /* Nos dice si hay un siguiente elemento. */
        @Override public boolean hasNext() {
            // Aquí va su código.
			return indice < elementos;
        }

        /* Regresa el siguiente elemento. */
        @Override public T next() {
            // Aquí va su código.
			if (indice >= elementos)
				throw new NoSuchElementException("No hay más elementos");
			indice++;
			return arbol[indice-1];
        }
    }

    /* Clase estática privada para adaptadores. */
    private static class Adaptador<T extends Comparable<T>> implements ComparableIndexable<Adaptador<T>> {

        /* El elemento. */
        private T elemento;
        /* El índice. */
        private int indice;

        /* Crea un nuevo comparable indexable. */
        public Adaptador(T elemento) {
            // Aquí va su código.
			this.elemento = elemento;
			indice = -1;
        }

        /* Regresa el índice. */
        @Override public int getIndice() {
            // Aquí va su código.
			return indice;
        }

        /* Define el índice. */
        @Override public void setIndice(int indice) {
            // Aquí va su código.
			this.indice = indice;
        }

        /* Compara un adaptador con otro. */
        @Override public int compareTo(Adaptador<T> adaptador) {
            // Aquí va su código.
			T otro = adaptador.elemento;
			return elemento.compareTo(otro);
        }
    }

    /* El número de elementos en el arreglo. */
    private int elementos;
    /* Usamos un truco para poder utilizar arreglos genéricos. */
    private T[] arbol;

    /* Truco para crear arreglos genéricos. Es necesario hacerlo así por cómo
       Java implementa sus genéricos; de otra forma obtenemos advertencias del
       compilador. */
    @SuppressWarnings("unchecked") private T[] nuevoArreglo(int n) {
        return (T[])(new ComparableIndexable[n]);
    }

    /**
     * Constructor sin parámetros. Es más eficiente usar {@link
     * #MonticuloMinimo(Coleccion)} o {@link #MonticuloMinimo(Iterable,int)},
     * pero se ofrece este constructor por completez.
     */
    public MonticuloMinimo() {
        // Aquí va su código.
		arbol = nuevoArreglo(100);
    }

    /**
     * Constructor para montículo mínimo que recibe una colección. Es más barato
     * construir un montículo con todos sus elementos de antemano (tiempo
     * <i>O</i>(<i>n</i>)), que el insertándolos uno por uno (tiempo
     * <i>O</i>(<i>n</i> log <i>n</i>)).
     * @param coleccion la colección a partir de la cuál queremos construir el
     *                  montículo.
     */
    public MonticuloMinimo(Coleccion<T> coleccion) {
        // Aquí va su código.
		this(coleccion, coleccion.getElementos());
    }

    /**
     * Constructor para montículo mínimo que recibe un iterable y el número de
     * elementos en el mismo. Es más barato construir un montículo con todos sus
     * elementos de antemano (tiempo <i>O</i>(<i>n</i>)), que el insertándolos
     * uno por uno (tiempo <i>O</i>(<i>n</i> log <i>n</i>)).
     * @param iterable el iterable a partir de la cuál queremos construir el
     *                 montículo.
     * @param n el número de elementos en el iterable.
     */
    public MonticuloMinimo(Iterable<T> iterable, int n) {
        // Aquí va su código.
		arbol = nuevoArreglo(n);
		elementos = n;
		int c = 0;
		for (T elemento : iterable) {
			arbol[c] = elemento;
			elemento.setIndice(c);
			c++;
		}
		int limite = (int) Math.floor(n/2)-1;
		for (int i = limite; i >= 0 ; i--)
            acomodaAbajo(arbol[i]);
    }

    /**
     * Agrega un nuevo elemento en el montículo.
     * @param elemento el elemento a agregar en el montículo.
     */
    @Override public void agrega(T elemento) {
        // Aquí va su código.
		if (arbol.length == elementos) {
			T[] temp = arbol;
			arbol = nuevoArreglo(elementos*2);
			for (int i = 0; i < elementos; i++)
				arbol[i] = temp[i];
		}
		arbol[elementos] = elemento;
		elemento.setIndice(elementos);
		elementos++;
		acomodaArriba(elemento);
    }

    /**
     * Elimina el elemento mínimo del montículo.
     * @return el elemento mínimo del montículo.
     * @throws IllegalStateException si el montículo es vacío.
     */
    @Override public T elimina() {
        // Aquí va su código.
		if(esVacia())
			throw new IllegalStateException("El montículo es vacío");
		T temp = arbol[0];
		elimina(temp);
		return temp;
    }

    /**
     * Elimina un elemento del montículo.
     * @param elemento a eliminar del montículo.
     */
    @Override public void elimina(T elemento) {
        // Aquí va su código.
		int i = elemento.getIndice();
		if ((elemento == null || esVacia()) || (i < 0 || i >= elementos))
            return;
        intercambia(i,elementos-1);
        arbol[elementos-1] = null;
        elementos--;
        acomodaArriba(arbol[i]);
        acomodaAbajo(arbol[i]);
        elemento.setIndice(-1);
    }

    /**
     * Nos dice si un elemento está contenido en el montículo.
     * @param elemento el elemento que queremos saber si está contenido.
     * @return <code>true</code> si el elemento está contenido,
     *         <code>false</code> en otro caso.
     */
    @Override public boolean contiene(T elemento) {
        // Aquí va su código.
		int x = elemento.getIndice();
		if (x >= elementos || x < 0)
			return false;
		return arbol[x].equals(elemento);
    }

    /**
     * Nos dice si el montículo es vacío.
     * @return <code>true</code> si ya no hay elementos en el montículo,
     *         <code>false</code> en otro caso.
     */
    @Override public boolean esVacia() {
        // Aquí va su código.
		return elementos <= 0;
    }

    /**
     * Limpia el montículo de elementos, dejándolo vacío.
     */
    @Override public void limpia() {
        // Aquí va su código.
		for (int i = 0; i < elementos-1; i++)
			arbol[i] = null;
		elementos = 0;
    }

   /**
     * Reordena un elemento en el árbol.
     * @param elemento el elemento que hay que reordenar.
     */
    @Override public void reordena(T elemento) {
        // Aquí va su código.
		int i = elemento.getIndice();
		if (i < 0 || i >= elementos)
			return;
		int padre = getPadre(i);
		acomodaArriba(elemento);
		acomodaAbajo(elemento);
    }

    /**
     * Regresa el número de elementos en el montículo mínimo.
     * @return el número de elementos en el montículo mínimo.
     */
    @Override public int getElementos() {
        // Aquí va su código.
		return elementos;
    }

    /**
     * Regresa el <i>i</i>-ésimo elemento del árbol, por niveles.
     * @param i el índice del elemento que queremos, en <em>in-order</em>.
     * @return el <i>i</i>-ésimo elemento del árbol, por niveles.
     * @throws NoSuchElementException si i es menor que cero, o mayor o igual
     *         que el número de elementos.
     */
    @Override public T get(int i) {
        // Aquí va su código.
		if (i < 0 || i >= elementos)
			throw new NoSuchElementException("El indice introducido es negativo o mayor al total");
		return arbol[i];
    }

    /**
     * Regresa una representación en cadena del montículo mínimo.
     * @return una representación en cadena del montículo mínimo.
     */
    @Override public String toString() {
        // Aquí va su código.
		String cadenaFinal = "";
		for (int i = 0; i < arbol.length; i++)
			cadenaFinal += arbol[i].toString() + ", ";
		return cadenaFinal;
    }

    /**
     * Nos dice si el montículo mínimo es igual al objeto recibido.
     * @param objeto el objeto con el que queremos comparar el montículo mínimo.
     * @return <code>true</code> si el objeto recibido es un montículo mínimo
     *         igual al que llama el método; <code>false</code> en otro caso.
     */
    @Override public boolean equals(Object objeto) {
        if (objeto == null || getClass() != objeto.getClass())
            return false;
        @SuppressWarnings("unchecked") MonticuloMinimo<T> monticulo = (MonticuloMinimo<T>) objeto;
        // Aquí va su código.
		if (monticulo.elementos != elementos)
			return false;
		/* Usamos try-catch en caso de que el otro arbol sea más pequeño */
		for (int i = 0; i < arbol.length; i++) {
			try {
				if (!arbol[i].equals(monticulo.arbol[i]))
					return false;
			} catch(ArrayIndexOutOfBoundsException e) {
				return false;
			}
		}
		return true;
    }

    /**
     * Regresa un iterador para iterar el montículo mínimo. El montículo se
     * itera en orden BFS.
     * @return un iterador para iterar el montículo mínimo.
     */
    @Override public Iterator<T> iterator() {
        return new Iterador();
    }

    /**
     * Ordena la colección usando HeapSort.
     * @param <T> tipo del que puede ser el arreglo.
     * @param coleccion la colección a ordenar.
     * @return una lista ordenada con los elementos de la colección.
     */
    public static <T extends Comparable<T>> Lista<T> heapSort(Coleccion<T> coleccion) {
        // Aquí va su código.
		Lista<Adaptador<T>> l1 = new Lista<>();
		for (T elemento : coleccion)
			l1.agregaFinal(new Adaptador<T>(elemento));
		MonticuloMinimo<Adaptador<T>> monty = new MonticuloMinimo<>(l1);
		Lista<T> l2 = new Lista<T>();
		while(!monty.esVacia()) {
			l2.agregaFinal(monty.get(0).elemento);
			monty.elimina();
		}
		return l2;
    }

	/***************************************FuncionesAuxiliares********************************************/

	/** Algoritmo auxiliar que acomoda el montículo hacia arriba
	 * Es recursivo. Nuestras clausulas de escape son cuando el elemento es nulo,
	 * cuando llegamos a la raíz o cuando el elemento está bien acomodado
	 * @param elemento El elemento desde el cual acomodaremos
	 */
	protected void acomodaArriba(T elemento) {
		if (elemento == null)
			return;
		int index = elemento.getIndice();
		int padre = getPadre(index);
		if (index <= 0 || arbol[padre].compareTo(arbol[index]) < 0)
			return;
		intercambia(index,padre);
		acomodaArriba(arbol[padre]);
	}

	/** Algoritmo auxiliar que acomoda el montículo hacia abajo
	 * Es recursivo. Nuestras clausulas de escape son cuando el elemento es nulo,
	 * cuando llegamos a alguna hoja o cuando el elemento está bien acomodado
	 * @param elemento El elemento desde el cual acomodaremos
	 */
	protected void acomodaAbajo(T elemento) {
		if (elemento == null)
			return;
		int i = elemento.getIndice();
		int izq = getIzquierdo(i);
        int der = getDerecho(i);
        int min = i;
        if (elementos <= i)
            return;
        if (izq < elementos && arbol[izq].compareTo(arbol[i]) < 0)
            min = izq;
        if (der < elementos && arbol[der].compareTo(arbol[min]) < 0)
            min = der;
        if (min == i)
            return;
		intercambia(i,min);
        acomodaAbajo(arbol[min]);
	}

	/**
	 * Método auxiliar que nos da el índice del padre de algún vértice de indice i
	 * @param i El índice del vértice hijo
	 * @return el indice de su padre
	 */
	protected int getPadre(int i) {
		return (int) Math.floor((i-1)/2);
	}

	/**
	 * Método auxiliar que nos da el índice del hijo derecho de algún vértice de indice i
	 * @param i El índice del vértice padre
	 * @return el indice de su hijo derecho
	 */
	protected int getDerecho(int i) {
		return 2*i+2;
	}

	/**
	 * Método auxiliar que nos da el índice del hijo izquierdo de algún vértice de indice i
	 * @param i El índice del vértice padre
	 * @return el indice de su hijo izquierdo
	 */
	protected int getIzquierdo(int i) {
		return 2*i+1;
	}

	/**
	 * Algoritmo para intercambiar dos vértices
	 * Al intercambiar dichos vértices también cambiamos sus índices
	 * @param x El índice de un vértice a intercambiar
	 * @param y El índice de el otro vértice a intercambiar
	 */
	protected void intercambia(int x, int y) {
		arbol[x].setIndice(y);
		arbol[y].setIndice(x);
		T temp = arbol[x];
		arbol[x] = arbol[y];
		arbol[y] = temp;
	}
}
