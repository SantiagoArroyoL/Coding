package mx.unam.ciencias.edd;

import java.lang.Math;
import java.lang.reflect.Array;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Clase para diccionarios (<em>hash tables</em>). Un diccionario generaliza el
 * concepto de arreglo, mapeando un conjunto de <em>llaves</em> a una colección
 * de <em>valores</em>.
 */
public class Diccionario<K, V> implements Iterable<V> {

    /* Clase interna privada para entradas. */
    private class Entrada {

        /* La llave. */
        public K llave;
        /* El valor. */
        public V valor;

        /* Construye una nueva entrada. */
        public Entrada(K llave, V valor) {
            // Aquí va su código.
			this.llave = llave;
			this.valor = valor;
        }

    }

    /* Clase interna privada para iteradores. */
    private class Iterador {

        /* En qué lista estamos. */
        private int indice;
        /* Iterador auxiliar. */
        private Iterator<Entrada> iterador;

        /* Construye un nuevo iterador, auxiliándose de las listas del
         * diccionario. */
        public Iterador() {
            // Aquí va su código.
			for (int i = 0; i < entradas.length; i++) {
				if (entradas[i] != null) {
					indice = i;
					iterador = entradas[i].iterator();
					return;
				}
			}
			iterador = null;
        }

        /* Nos dice si hay una siguiente entrada. */
        public boolean hasNext() {
            // Aquí va su código.
			return iterador != null;
        }

        /* Regresa la siguiente entrada. */
        public Entrada siguiente() {
            // Aquí va su código.
			if (iterador == null)
				throw new NoSuchElementException("El siguiente elemento es vacío");
			Entrada e = iterador.next();
			if (!iterador.hasNext())
				mueveIterador();
			return e;
        }

        /* Mueve el iterador a la siguiente entrada válida. */
        private void mueveIterador() {
            // Aquí va su código.
			for (int i = indice+1; i < entradas.length; i++) {
				if (entradas[i] != null){
					indice = i;
					iterador = entradas[i].iterator();
					return;
				}
			}
			iterador = null;
        }
    }

    /* Clase interna privada para iteradores de llaves. */
    private class IteradorLlaves extends Iterador implements Iterator<K> {

        /* Regresa el siguiente elemento. */
        @Override public K next() {
            // Aquí va su código.
			return siguiente().llave;
        }
    }

    /* Clase interna privada para iteradores de valores. */
    private class IteradorValores extends Iterador implements Iterator<V> {

        /* Regresa el siguiente elemento. */
        @Override public V next() {
            // Aquí va su código.
			return siguiente().valor;
        }
    }

    /** Máxima carga permitida por el diccionario. */
    public static final double MAXIMA_CARGA = 0.72;

    /* Capacidad mínima; decidida arbitrariamente a 2^6. */
    private static final int MINIMA_CAPACIDAD = 64;

    /* Dispersor. */
    private Dispersor<K> dispersor;
    /* Nuestro diccionario. */
    private Lista<Entrada>[] entradas;
    /* Número de valores. */
    private int elementos;

    /* Truco para crear un arreglo genérico. Es necesario hacerlo así por cómo
       Java implementa sus genéricos; de otra forma obtenemos advertencias del
       compilador. */
    @SuppressWarnings("unchecked")
    private Lista<Entrada>[] nuevoArreglo(int n) {
        return (Lista<Entrada>[])Array.newInstance(Lista.class, n);
    }

    /**
     * Construye un diccionario con una capacidad inicial y dispersor
     * predeterminados.
     */
    public Diccionario() {
        this(MINIMA_CAPACIDAD, (K llave) -> llave.hashCode());
    }

    /**
     * Construye un diccionario con una capacidad inicial definida por el
     * usuario, y un dispersor predeterminado.
     * @param capacidad la capacidad a utilizar.
     */
    public Diccionario(int capacidad) {
        this(capacidad, (K llave) -> llave.hashCode());
    }

    /**
     * Construye un diccionario con una capacidad inicial predeterminada, y un
     * dispersor definido por el usuario.
     * @param dispersor el dispersor a utilizar.
     */
    public Diccionario(Dispersor<K> dispersor) {
        this(MINIMA_CAPACIDAD, dispersor);
    }

    /**
     * Construye un diccionario con una capacidad inicial y un método de
     * dispersor definidos por el usuario.
     * @param capacidad la capacidad inicial del diccionario.
     * @param dispersor el dispersor a utilizar.
     */
    public Diccionario(int capacidad, Dispersor<K> dispersor) {
        // Aquí va su código.
		this.dispersor = dispersor;
		if (capacidad < MINIMA_CAPACIDAD)
			capacidad = MINIMA_CAPACIDAD;
		int n = log2(capacidad*2);
		entradas = nuevoArreglo((int)Math.pow(2,n));
		for (int i = 0; i < entradas.length; i++)
			entradas[i] = null;
		elementos = 0;
    }

    /**
     * Agrega un nuevo valor al diccionario, usando la llave proporcionada. Si
     * la llave ya había sido utilizada antes para agregar un valor, el
     * diccionario reemplaza ese valor con el recibido aquí.
     * @param llave la llave para agregar el valor.
     * @param valor el valor a agregar.
     * @throws IllegalArgumentException si la llave o el valor son nulos.
     */
    public void agrega(K llave, V valor) {
        // Aquí va su código.
		if (llave == null || valor == null)
			throw new IllegalArgumentException("La llave o el valor introducidos son nulos!");
		int i = dispersaMascara(llave);
        if (entradas[i] == null)
            entradas[i] = new Lista<Entrada>();
        for (Entrada e : entradas[i]) {
            if (e.llave.equals(llave)) {
                e.valor = valor;
                return;
            }
		}
        entradas[i].agrega(new Entrada(llave,valor));
        elementos++;
		if (carga() >= MAXIMA_CARGA) {
			elementos = 0;
			Lista<Entrada>[] temp = entradas;
			entradas = nuevoArreglo(temp.length*2);
			for (int j = 0; j < temp.length; j++) {
				if(temp[j] != null) {
					for (Entrada e : temp[j]) {
						agrega(e.llave, e.valor);
					}
				}
			}
		}
    }

    /**
     * Regresa el valor del diccionario asociado a la llave proporcionada.
     * @param llave la llave para buscar el valor.
     * @return el valor correspondiente a la llave.
     * @throws IllegalArgumentException si la llave es nula.
     * @throws NoSuchElementException si la llave no está en el diccionario.
     */
    public V get(K llave) {
        // Aquí va su código.
		if (llave == null)
			throw new IllegalArgumentException("La llave introducida es nula");
		int i = dispersaMascara(llave);
		if (entradas[i] == null)
			throw new NoSuchElementException("La llave no está en el diccionario");
		for (Entrada e : entradas[i])
			if(e.llave.equals(llave))
				return e.valor;
		throw new NoSuchElementException("La llave no está en el diccionario");
    }

    /**
     * Nos dice si una llave se encuentra en el diccionario.
     * @param llave la llave que queremos ver si está en el diccionario.
     * @return <code>true</code> si la llave está en el diccionario,
     *         <code>false</code> en otro caso.
     */
    public boolean contiene(K llave) {
        // Aquí va su código.
		if (llave == null)
			return false;
		int i = dispersaMascara(llave);
		if (entradas[i] == null)
			return false;
		for (Entrada e : entradas[i]) {
			if(e.llave.equals(llave))
				return true;
		}
		return false;
    }

    /**
     * Elimina el valor del diccionario asociado a la llave proporcionada.
     * @param llave la llave para buscar el valor a eliminar.
     * @throws IllegalArgumentException si la llave es nula.
     * @throws NoSuchElementException si la llave no se encuentra en
     *         el diccionario.
     */
    public void elimina(K llave) {
        // Aquí va su código.
		if (llave == null)
			throw new IllegalArgumentException("La llave introducida es nula");
		int i = dispersaMascara(llave);
		if (entradas[i] == null)
			throw new NoSuchElementException("La llave no está en el diccionario");
		for (Entrada e : entradas[i]) {
			if (e.llave.equals(llave)) {
				entradas[i].elimina(e);
				elementos--;
				if (entradas[i].esVacia())
					entradas[i] = null;
				return;
			}
		}
		throw new NoSuchElementException("La llave no está en el diccionario");
    }

    /**
     * Nos dice cuántas colisiones hay en el diccionario.
     * @return cuántas colisiones hay en el diccionario.
     */
    public int colisiones() {
        // Aquí va su código.
		int suma = 0;
		for (int i = 0; i < entradas.length; i++)
			if (entradas[i] != null)
				suma += entradas[i].getLongitud();
		if (suma == 0)
			return suma;
		return suma-1;
    }

    /**
     * Nos dice el máximo número de colisiones para una misma llave que tenemos
     * en el diccionario.
     * @return el máximo número de colisiones para una misma llave.
     */
    public int colisionMaxima() {
        // Aquí va su código.
		int max = 0;
		for (int i = 0; i < entradas.length; i++)
			if (entradas[i] != null && entradas[i].getLongitud() > max)
				max = entradas[i].getLongitud();
		return max-1;
    }

    /**
     * Nos dice la carga del diccionario.
     * @return la carga del diccionario.
     */
    public double carga() {
        // Aquí va su código.
		return ((double) elementos) / entradas.length;
    }

    /**
     * Regresa el número de entradas en el diccionario.
     * @return el número de entradas en el diccionario.
     */
    public int getElementos() {
        // Aquí va su código.
		return elementos;
    }

    /**
     * Nos dice si el diccionario es vacío.
     * @return <code>true</code> si el diccionario es vacío, <code>false</code>
     *         en otro caso.
     */
    public boolean esVacia() {
        // Aquí va su código.
		return elementos <= 0;
    }

    /**
     * Limpia el diccionario de elementos, dejándolo vacío.
     */
    public void limpia() {
        // Aquí va su código
		entradas = nuevoArreglo(entradas.length);
		elementos = 0;
    }

    /**
     * Regresa una representación en cadena del diccionario.
     * @return una representación en cadena del diccionario.
     */
    @Override public String toString() {
        // Aquí va su código.
		if (esVacia())
			return "{}";
		String sFinal = "{ ";
		for (int i = 0; i < entradas.length; i++) {
			if (entradas[i] != null) {
				for (Entrada e : entradas[i]) {
					sFinal += "\'" + e.llave.toString() + "\': ";
					sFinal += "\'" + e.valor.toString() + "\', ";
				}
			}
		}
		return sFinal + "}";
    }

    /**
     * Nos dice si el diccionario es igual al objeto recibido.
     * @param o el objeto que queremos saber si es igual al diccionario.
     * @return <code>true</code> si el objeto recibido es instancia de
     *         Diccionario, y tiene las mismas llaves asociadas a los mismos
     *         valores.
     */
    @Override public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass())
            return false;
        @SuppressWarnings("unchecked") Diccionario<K, V> d = (Diccionario<K, V>)o;
        // Aquí va su código.
		if (elementos != d.elementos)
			return false;
		/* Usamos try-catch en caso de que el otro diccionario sea más pequeño */
		for (int i = 0; i < entradas.length; i++) {
			if (entradas[i] != null) {
				for (Entrada e : entradas[i]) {
					if (!d.contiene(e.llave)) {
						return false;
					} else if (!e.valor.equals(d.get(e.llave))){
						return false;
					}
				}
			}
		}
		return true;
    }

    /**
     * Regresa un iterador para iterar las llaves del diccionario. El
     * diccionario se itera sin ningún orden específico.
     * @return un iterador para iterar las llaves del diccionario.
     */
    public Iterator<K> iteradorLlaves() {
        return new IteradorLlaves();
    }

    /**
     * Regresa un iterador para iterar los valores del diccionario. El
     * diccionario se itera sin ningún orden específico.
     * @return un iterador para iterar los valores del diccionario.
     */
    @Override public Iterator<V> iterator() {
        return new IteradorValores();
    }

	/***************************************Funciones Auxiliares********************************************/

	/**
	 * Método auxiliar para calcular el techo de logaritmos de base 2
	 * @param x El número entero a calcular
	 * @return El techo del logaritmo base 2 del entero recibido
	 */
	private int log2(int x) {
    	return (int) Math.ceil(Math.log(x) / Math.log(2));
	}

	/**
	 * Método auxiliar que dispersa una llave recibida aunado a
	 * la máscara del diccionario
	 * La máscara siempre será el tamaño del arreglo menos uno
	 * @param llave La llave a dispersar
	 * @return Un entero de 32 bits con la dispersión de la llave
	 *		    recibida con la máscara
	 */
	private int dispersaMascara(K llave) {
		return llave.hashCode() & (entradas.length-1);
	}
}
