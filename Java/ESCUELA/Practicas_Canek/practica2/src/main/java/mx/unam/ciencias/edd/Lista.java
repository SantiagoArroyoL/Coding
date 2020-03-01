package mx.unam.ciencias.edd;

import java.util.Comparator;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * <p>Clase genérica para listas doblemente ligadas.</p>
 *
 * <p>Las listas nos permiten agregar elementos al inicio o final de la lista,
 * eliminar elementos de la lista, comprobar si un elemento está o no en la
 * lista, y otras operaciones básicas.</p>
 *
 * <p>Las listas no aceptan a <code>null</code> como elemento.</p>
 *
 * @param <T> El tipo de los elementos de la lista.
 */
public class Lista<T> implements Coleccion<T> {

    /* Clase interna privada para nodos. */
    private class Nodo {
        /* El elemento del nodo. */
        public T elemento;
        /* El nodo anterior. */
        public Nodo anterior;
        /* El nodo siguiente. */
        public Nodo siguiente;

        /* Construye un nodo con un elemento. */
        public Nodo(T elemento) {
            // Aquí va su código.
			this.elemento = elemento;
        }
    }

    /* Clase interna privada para iteradores. */
    private class Iterador implements IteradorLista<T> {
        /* El nodo anterior. */
        public Nodo anterior;
        /* El nodo siguiente. */
        public Nodo siguiente;

        /* Construye un nuevo iterador. */
        public Iterador() {
            // Aquí va su código.
			siguiente = cabeza;
			anterior = null;
        }

        /* Nos dice si hay un elemento siguiente. */
        @Override public boolean hasNext() {
            // Aquí va su código.
			return siguiente != null;
        }

        /* Nos da el elemento siguiente. */
        @Override public T next() {
            // Aquí va su código.
			if (siguiente == null)
				throw new NoSuchElementException("El siguiente elemento es vacío");
			anterior = siguiente;
			siguiente = siguiente.siguiente;
			return anterior.elemento;
        }

        /* Nos dice si hay un elemento anterior. */
        @Override public boolean hasPrevious() {
            // Aquí va su código.
			return anterior != null;
        }

        /* Nos da el elemento anterior. */
        @Override public T previous() {
            // Aquí va su código.
			if (anterior == null)
				throw new NoSuchElementException("El anterior elemento es vacío");
			siguiente = anterior;
			anterior = anterior.anterior;
			return siguiente.elemento;
        }

        /* Mueve el iterador al inicio de la lista. */
        @Override public void start() {
            // Aquí va su código.
			siguiente = cabeza;
			anterior = null;
        }

        /* Mueve el iterador al final de la lista. */
        @Override public void end() {
            // Aquí va su código.
			siguiente = null;
			anterior = rabo;
        }
    }

    /* Primer elemento de la lista. */
    private Nodo cabeza;
    /* Último elemento de la lista. */
    private Nodo rabo;
    /* Número de elementos en la lista. */
    private int longitud;

    /**
     * Regresa la longitud de la lista. El método es idéntico a {@link
     * #getElementos}.
     * @return la longitud de la lista, el número de elementos que contiene.
     */
    public int getLongitud() {
        // Aquí va su código.
		return longitud;
    }

    /**
     * Regresa el número elementos en la lista. El método es idéntico a {@link
     * #getLongitud}.
     * @return el número elementos en la lista.
     */
    @Override public int getElementos() {
        // Aquí va su código.
		return longitud;
    }

    /**
     * Nos dice si la lista es vacía.
     * @return <code>true</code> si la lista es vacía, <code>false</code> en
     *         otro caso.
     */
    @Override public boolean esVacia() {
        // Aquí va su código.
		return cabeza == null;
    }

    /**
     * Agrega un elemento a la lista. Si la lista no tiene elementos, el
     * elemento a agregar será el primero y último. El método es idéntico a
     * {@link #agregaFinal}.
     * @param elemento el elemento a agregar.
     * @throws IllegalArgumentException si <code>elemento</code> es
     *         <code>null</code>.
     */
    @Override public void agrega(T elemento) {
        // Aquí va su código.
		if (elemento == null)
			throw new IllegalArgumentException("No puedes agregar un elemento que sea null!");
		Nodo nuevo = new Nodo(elemento);
		if (rabo == null) {
			cabeza = rabo = nuevo;
		} else {
			rabo.siguiente = nuevo;
		    nuevo.anterior = rabo;
		    rabo = nuevo;
		}
		longitud++;
    }

    /**
     * Agrega un elemento al final de la lista. Si la lista no tiene elementos,
     * el elemento a agregar será el primero y último.
     * @param elemento el elemento a agregar.
     * @throws IllegalArgumentException si <code>elemento</code> es
     *         <code>null</code>.
     */
    public void agregaFinal(T elemento) {
        // Aquí va su código.
		if (elemento == null)
			throw new IllegalArgumentException("No puedes agregar un elemento que sea null!");
		Nodo nuevo = new Nodo(elemento);
		if (rabo == null) {
			cabeza = rabo = nuevo;
		} else {
			rabo.siguiente = nuevo;
	   	    nuevo.anterior = rabo;
	   	    rabo = nuevo;
		}
		longitud++;
    }

    /**
     * Agrega un elemento al inicio de la lista. Si la lista no tiene elementos,
     * el elemento a agregar será el primero y último.
     * @param elemento el elemento a agregar.
     * @throws IllegalArgumentException si <code>elemento</code> es
     *         <code>null</code>.
     */
    public void agregaInicio(T elemento) {
        // Aquí va su código.
		if (elemento == null)
			throw new IllegalArgumentException("No puedes agregar un elemento que sea null!");
		Nodo nuevo = new Nodo(elemento);
		if (cabeza == null) {
			cabeza = rabo = nuevo;
		} else {
			cabeza.anterior = nuevo;
		    nuevo.siguiente = cabeza;
		    cabeza = nuevo;
		}
		longitud++;
    }

    /**
     * Inserta un elemento en un índice explícito.
     *
     * Si el índice es menor o igual que cero, el elemento se agrega al inicio
     * de la lista. Si el índice es mayor o igual que el número de elementos en
     * la lista, el elemento se agrega al fina de la misma. En otro caso,
     * después de mandar llamar el método, el elemento tendrá el índice que se
     * especifica en la lista.
     * @param i el índice dónde insertar el elemento. Si es menor que 0 el
     *          elemento se agrega al inicio de la lista, y si es mayor o igual
     *          que el número de elementos en la lista se agrega al final.
     * @param elemento el elemento a insertar.
     * @throws IllegalArgumentException si <code>elemento</code> es
     *         <code>null</code>.
     */
    public void inserta(int i, T elemento) {
        // Aquí va su código.
		if (elemento == null)
			throw new IllegalArgumentException("No puedes agregar un elemento que sea null!");
		Nodo nuevo = new Nodo(elemento);
		if (i <= 0) {
			agregaInicio(elemento);
		} else if (i >= longitud) {
			agregaFinal(elemento);
		} else if (cabeza == null) {
			cabeza = rabo = nuevo;
		} else {
			longitud++;
			Nodo n = new Nodo(elemento);
			Nodo m = cabeza;
			int j = 0;
			while (j++ < i) {
				m = m.siguiente;
			}
			m.anterior.siguiente = n;
			n.anterior = m.anterior;
			m.anterior = n;
			n.siguiente = m;
		}
    }

    /**
     * Elimina un elemento de la lista. Si el elemento no está contenido en la
     * lista, el método no la modifica.
     * @param elemento el elemento a eliminar.
     */
    @Override public void elimina(T elemento) {
        // Aquí va su código.
		if (longitud == 0 || !contiene(elemento))
	    	return;
		if (indiceDe(elemento) == 0) {
			eliminaPrimero();
			return;
		}
		if (indiceDe(elemento) == longitud - 1) {
			eliminaUltimo();
			return;
		}
	    Nodo n = buscaNodo(elemento, cabeza);
	    n.siguiente.anterior = n.anterior;
       	n.anterior.siguiente = n.siguiente;
       	longitud--;
    }

    /**
     * Elimina el primer elemento de la lista y lo regresa.
     * @return el primer elemento de la lista antes de eliminarlo.
     * @throws NoSuchElementException si la lista es vacía.
     */
    public T eliminaPrimero() {
        // Aquí va su código.
		if (longitud == 0)
			throw new NoSuchElementException("La lista es vacía");
		T temp = cabeza.elemento;
		if (longitud == 1) {
		    cabeza = rabo = null;
			longitud--;
			return temp;
		}
		Nodo n = cabeza;
		cabeza = n.siguiente;
		n.siguiente = null;
		cabeza.anterior = null;
		longitud--;
		return temp;
    }

    /**
     * Elimina el último elemento de la lista y lo regresa.
     * @return el último elemento de la lista antes de eliminarlo.
     * @throws NoSuchElementException si la lista es vacía.
     */
    public T eliminaUltimo() {
        // Aquí va su código.
		if (longitud == 0)
			throw new NoSuchElementException("La lista es vacía");
		T temp = rabo.elemento;
		if(longitud == 1) {
			cabeza = rabo = null;
			longitud--;
			return temp;
		}
		Nodo n = rabo;
		rabo = n.anterior;
		n.anterior = rabo.siguiente = null;
		longitud--;
		return temp;
    }

    /**
     * Nos dice si un elemento está en la lista.
     * @param elemento el elemento que queremos saber si está en la lista.
     * @return <code>true</code> si <code>elemento</code> está en la lista,
     *         <code>false</code> en otro caso.
     */
    @Override public boolean contiene(T elemento) {
        // Aquí va su código.
		return buscaNodo(elemento, cabeza) != null;
    }

    /**
     * Regresa la reversa de la lista.
     * @return una nueva lista que es la reversa la que manda llamar el método.
     */
    public Lista<T> reversa() {
        // Aquí va su código.
		Lista<T> arreglo = new Lista<>();
		if (longitud == 0)
			return arreglo;
		int cont = 0;
		Nodo n = rabo;
		while(cont < longitud) {
			arreglo.agrega(n.elemento);
			n = n.anterior;
			cont++;
		}
		return arreglo;
    }

    /**
     * Regresa una copia de la lista. La copia tiene los mismos elementos que la
     * lista que manda llamar el método, en el mismo orden.
     * @return una copiad de la lista.
     */
    public Lista<T> copia() {
        // Aquí va su código.
		Lista<T> arreglo = new Lista<>();
		if (longitud == 0)
			return arreglo;
		int cont = 0;
		Nodo n = cabeza;
		while(cont < longitud){
			arreglo.agrega(n.elemento);
			n = n.siguiente;
			cont++;
		}
		return arreglo;
    }

    /**
     * Limpia la lista de elementos, dejándola vacía.
     */
    @Override public void limpia() {
        // Aquí va su código.
		cabeza = rabo = null;
		longitud = 0;
    }

    /**
     * Regresa el primer elemento de la lista.
     * @return el primer elemento de la lista.
     * @throws NoSuchElementException si la lista es vacía.
     */
    public T getPrimero() {
        // Aquí va su código.
		if (longitud == 0)
			throw new NoSuchElementException("La lista esta vacía");
		return cabeza.elemento;
    }

    /**
     * Regresa el último elemento de la lista.
     * @return el primer elemento de la lista.
     * @throws NoSuchElementException si la lista es vacía.
     */
    public T getUltimo() {
        // Aquí va su código.
		if (longitud == 0)
			throw new NoSuchElementException("La lista esta vacía");
		return rabo.elemento;
    }

    /**
     * Regresa el <em>i</em>-ésimo elemento de la lista.
     * @param i el índice del elemento que queremos.
     * @return el <em>i</em>-ésimo elemento de la lista.
     * @throws ExcepcionIndiceInvalido si <em>i</em> es menor que cero o mayor o
     *         igual que el número de elementos en la lista.
     */
    public T get(int i) {
        // Aquí va su código.
		if (i < 0 || i >= longitud)
			throw new ExcepcionIndiceInvalido("Él indice que introduciste no es válido");
		int cont = 0;
		Nodo n = cabeza;
		while (cont < i) {
			n = n.siguiente;
			cont++;
		}
		return n.elemento;
    }

    /**
     * Regresa el índice del elemento recibido en la lista.
     * @param elemento el elemento del que se busca el índice.
     * @return el índice del elemento recibido en la lista, o -1 si el elemento
     *         no está contenido en la lista.
     */
    public int indiceDe(T elemento) {
        // Aquí va su código.
		if (!contiene(elemento) || longitud == 0)
			return -1;
		Nodo aux = this.cabeza;
		int cont = 0;
		return indiceDe(elemento, aux, cont);
    }

    /**
     * Regresa una representación en cadena de la lista.
     * @return una representación en cadena de la lista.
     */
    @Override public String toString() {
        // Aquí va su código.
		if (longitud == 0)
			return "[]";
		Nodo n = cabeza;
		String cadenaFinal = "[";
		while (n != rabo) {
			cadenaFinal += n.elemento + ", ";
			n = n.siguiente;
		}
		return cadenaFinal + n.elemento + "]";
    }

    /**
     * Nos dice si la lista es igual al objeto recibido.
     * @param objeto el objeto con el que hay que comparar.
     * @return <code>true</code> si la lista es igual al objeto recibido;
     *         <code>false</code> en otro caso.
     */
    @Override public boolean equals(Object objeto) {
		if (objeto == null || getClass() != objeto.getClass())
            return false;
        @SuppressWarnings("unchecked") Lista<T> lista = (Lista<T>) objeto;
        // Aquí va su código.
		if (longitud != lista.getLongitud())
			return false;
		Nodo copia = lista.cabeza;
		Nodo n = cabeza;
		int cont = 0;
		while (cont < longitud) {
			if (!n.elemento.equals(copia.elemento))
				return false;
			n = n.siguiente;
			copia = copia.siguiente;
			cont++;
		}
		return true;
    }

    /**
     * Regresa un iterador para recorrer la lista en una dirección.
     * @return un iterador para recorrer la lista en una dirección.
     */
    @Override public Iterator<T> iterator() {
        return new Iterador();
    }

    /**
     * Regresa un iterador para recorrer la lista en ambas direcciones.
     * @return un iterador para recorrer la lista en ambas direcciones.
     */
    public IteradorLista<T> iteradorLista() {
        return new Iterador();
    }

    /**
     * Regresa una copia de la lista, pero ordenada. Para poder hacer el
     * ordenamiento, el método necesita una instancia de {@link Comparator} para
     * poder comparar los elementos de la lista.
     * @param comparador el comparador que la lista usará para hacer el
     *                   ordenamiento.
     * @return una copia de la lista, pero ordenada.
     */
    public Lista<T> mergeSort(Comparator<T> comparador) {
		Lista<T> copia = copia();
		return mergeSortAux(copia, comparador);
	}

	/**
     * Método Auxiliar recursivo para MergeSort
     * @param lista La lista a ser ordenada
     * @param comparador el comparador que la lista usará para hacer el ordenamiento.
     * @return una copia de la lista recibida, pero ordenada.
     */
	private  Lista<T> mergeSortAux(Lista<T> lista, Comparator<T> comparador){
        // Aquí va su código
		if(lista.longitud <= 1)
			return lista;
	    Lista<T> listaIzquierda = new Lista<>();
	    Lista<T> listaDerecha = new Lista<>();
	    Nodo a = lista.cabeza;
	    Nodo b = a;
	    for (int i = 0; i < lista.longitud; i++) {
		    if (i < lista.longitud / 2) {
		    	listaIzquierda.agrega(a.elemento);
				a = a.siguiente;
				b = a;
		    } else {
				listaDerecha.agrega(b.elemento);
				b = b.siguiente;
			}
	    }
		listaIzquierda = mergeSortAux(listaIzquierda, comparador);
		listaDerecha = mergeSortAux(listaDerecha, comparador);
		return mezcla(listaIzquierda, listaDerecha, comparador);
    }

	/**
     * Método Auxiliar que junta dos listas ordenadas
     * @param izquierda La lista 1 a ser mezclada
     * @param derecha La lista 2 a ser mezclada
     * @param comparador el comparador que la lista usará para hacer el ordenamiento.
     * @return La unión de las 2 listas anteriores ordenada
     */
    private Lista<T> mezcla(Lista<T> izquierda, Lista<T> derecha, Comparator<T> comparador) {
		Lista<T> ordenada = new Lista<T>();
		Nodo i = izquierda.cabeza;
		Nodo j = derecha.cabeza;
		while (i != null && j != null) {
			if (comparador.compare(i.elemento, j.elemento) <= 0) {
				ordenada.agrega(i.elemento);
				i = i.siguiente;
			} else {
				ordenada.agrega(j.elemento);
				j = j.siguiente;
			}
		}
		if (i == null) {
			while (j != null) {
				ordenada.agrega(j.elemento);
				j = j.siguiente;
			}
		} else {
			while (i != null) {
				ordenada.agrega(i.elemento);
				i = i.siguiente;
			}
		}
		return ordenada;
    }

    /**
     * Regresa una copia de la lista recibida, pero ordenada. La lista recibida
     * tiene que contener nada más elementos que implementan la interfaz {@link
     * Comparable}.
     * @param <T> tipo del que puede ser la lista.
     * @param lista la lista que se ordenará.
     * @return una copia de la lista recibida, pero ordenada.
     */
    public static <T extends Comparable<T>> Lista<T> mergeSort(Lista<T> lista) {
        return lista.mergeSort((a, b) -> a.compareTo(b));
    }

    /**
     * Busca un elemento en la lista ordenada, usando el comparador recibido. El
     * método supone que la lista está ordenada usando el mismo comparador.
     * @param elemento el elemento a buscar.
     * @param comparador el comparador con el que la lista está ordenada.
     * @return <code>true</code> si el elemento está contenido en la lista,
     *         <code>false</code> en otro caso.
     */
    public boolean busquedaLineal(T elemento, Comparator<T> comparador) {
        // Aquí va su código.
		// Lista<T> copia = copia();
		for (T temp : this){
			if (comparador.compare(elemento, temp) < 0)
				return false;
			if (comparador.compare(elemento, temp) == 0)
				return true;
		}
		return false;
    }

    /**
     * Busca un elemento en una lista ordenada. La lista recibida tiene que
     * contener nada más elementos que implementan la interfaz {@link
     * Comparable}, y se da por hecho que está ordenada.
     * @param <T> tipo del que puede ser la lista.
     * @param lista la lista donde se buscará.
     * @param elemento el elemento a buscar.
     * @return <code>true</code> si el elemento está contenido en la lista,
     *         <code>false</code> en otro caso.
     */
    public static <T extends Comparable<T>> boolean busquedaLineal(Lista<T> lista, T elemento) {
        return lista.busquedaLineal(elemento, (a, b) -> a.compareTo(b));
    }

	/***************************************Funciones Auxiliares********************************************/

	/**
	 * Busca un nodo dentro de la lista basandose en el elemento que contenga.
	 * @param e Objeto que será buscado en la lista
	 * @param n El nodo donde se esta buscando actualmente
	 * @return El nodo donde se encuentra el elemento.
	 */
    private Nodo buscaNodo(Object e, Nodo n){
	    if (n == null)
		    return null;
	    return n.elemento.equals(e) ? n : buscaNodo(e, n.siguiente);
		//Como elemento es de tipo genérico, el método equals dependerá de cada tipo
    }

	/**
     * Regresa el índice del elemento recibido en la lista.
	 * @param elemento El elemento a buscar en la lista
	 * @param n El nodo donde se esta buscando actualmente
	 * @param cont El indice que indica a partir de dónde en la lista se buscará
     * @return el índice del elemento recibido en la lista.
     */
    private int indiceDe(Object elemento, Nodo n, int cont) {
		if (n == null)
		    return -1;
		return (n.elemento.equals(elemento)) ? cont : indiceDe(elemento, n.siguiente, ++cont);
    }

}
