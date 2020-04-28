package mx.unam.ciencias.edd;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Clase para gráficas. Una gráfica es un conjunto de vértices y aristas, tales
 * que las aristas son un subconjunto del producto cruz de los vértices.
 */
public class Grafica<T> implements Coleccion<T> {

    /* Clase interna privada para iteradores. */
    private class Iterador implements Iterator<T> {

        /* Iterador auxiliar. */
        private Iterator<Vertice> iterador;

        /* Construye un nuevo iterador, auxiliándose de la lista de vértices. */
        public Iterador() {
            iterador = vertices.iterator();
        }

        /* Nos dice si hay un siguiente elemento. */
        @Override public boolean hasNext() {
            // Aquí va su código.
			return iterador.hasNext();
        }

        /* Regresa el siguiente elemento. */
        @Override public T next() {
            // Aquí va su código.
			return iterador.next().get();
        }
    }

    /* Clase interna privada para vértices. */
    private class Vertice implements VerticeGrafica<T> {

        /* El elemento del vértice. */
        public T elemento;
        /* El color del vértice. */
        public Color color;
        /* La lista de vecinos del vértice. */
        public Lista<Vertice> vecinos;

        /* Crea un nuevo vértice a partir de un elemento. */
        public Vertice(T elemento) {
            // Aquí va su código.
			this.elemento = elemento;
			color = Color.NINGUNO;
			vecinos = new Lista<>();
        }

        /* Regresa el elemento del vértice. */
        @Override public T get() {
            // Aquí va su código.
			return elemento;
        }

        /* Regresa el grado del vértice. */
        @Override public int getGrado() {
            // Aquí va su código.
			return vecinos.getLongitud();
        }

        /* Regresa el color del vértice. */
        @Override public Color getColor() {
            // Aquí va su código.
			return color;
        }

        /* Regresa un iterable para los vecinos. */
        @Override public Iterable<? extends VerticeGrafica<T>> vecinos() {
            // Aquí va su código.
			return vecinos;
        }
    }

    /* Vértices. */
    private Lista<Vertice> vertices;
    /* Número de aristas. */
    private int aristas;

    /**
     * Constructor único.
     */
    public Grafica() {
        // Aquí va su código.
		vertices = new Lista<>();
    }

    /**
     * Regresa el número de elementos en la gráfica. El número de elementos es
     * igual al número de vértices.
     * @return el número de elementos en la gráfica.
     */
    @Override public int getElementos() {
        // Aquí va su código.
		return vertices.getElementos();
    }

    /**
     * Regresa el número de aristas.
     * @return el número de aristas.
     */
    public int getAristas() {
        // Aquí va su código.
		return aristas;
    }

    /**
     * Agrega un nuevo elemento a la gráfica.
     * @param elemento el elemento a agregar.
     * @throws IllegalArgumentException si el elemento es <code>null</code> o ya
     *         había sido agregado a la gráfica.
     */
    @Override public void agrega(T elemento) {
        // Aquí va su código.
		if (elemento == null || contiene(elemento))
			throw new IllegalArgumentException("El elemento a agregar es nulo o ya esta en la gráfica");
		vertices.agrega(new Vertice(elemento));
    }

    /**
     * Conecta dos elementos de la gráfica. Los elementos deben estar en la
     * gráfica. El peso de la arista que conecte a los elementos será 1.
     * @param a el primer elemento a conectar.
     * @param b el segundo elemento a conectar.
     * @throws NoSuchElementException si a o b no son elementos de la gráfica.
     * @throws IllegalArgumentException si a o b ya están conectados, o si a es
     *         igual a b.
     */
    public void conecta(T a, T b) {
        // Aquí va su código.
		if (a.equals(b) || sonVecinos(a,b))
			throw new IllegalArgumentException("Ambos elementos son iguales o ya son vecinos");
		Vertice v = (Vertice) vertice(a);
		Vertice u = (Vertice) vertice(b);
		aristas++;
		v.vecinos.agrega(u);
		u.vecinos.agrega(v);
    }

    /**
     * Desconecta dos elementos de la gráfica. Los elementos deben estar en la
     * gráfica y estar conectados entre ellos.
     * @param a el primer elemento a desconectar.
     * @param b el segundo elemento a desconectar.
     * @throws NoSuchElementException si a o b no son elementos de la gráfica.
     * @throws IllegalArgumentException si a o b no están conectados.
     */
    public void desconecta(T a, T b) {
        // Aquí va su código.
		if (a.equals(b) || !sonVecinos(a,b))
			throw new IllegalArgumentException("Ambos elementos son iguales o no son vecinos");
		Vertice v = (Vertice) vertice(a);
		Vertice u = (Vertice) vertice(b);
		aristas--;
		v.vecinos.elimina(u);
		u.vecinos.elimina(v);
    }

    /**
     * Nos dice si el elemento está contenido en la gráfica.
     * @return <code>true</code> si el elemento está contenido en la gráfica,
     *         <code>false</code> en otro caso.
     */
    @Override public boolean contiene(T elemento) {
        // Aquí va su código.
		for (Vertice v : vertices )
            if (v.elemento.equals(elemento))
                return true;
        return false;
    }

    /**
     * Elimina un elemento de la gráfica. El elemento tiene que estar contenido
     * en la gráfica.
     * @param elemento el elemento a eliminar.
     * @throws NoSuchElementException si el elemento no está contenido en la
     *         gráfica.
     */
    @Override public void elimina(T elemento) {
        // Aquí va su código.
		Vertice v = (Vertice) vertice(elemento);
		vertices.elimina(v);
		for (Vertice u : v.vecinos) {
			aristas--;
			u.vecinos.elimina(v);
		}
    }

    /**
     * Nos dice si dos elementos de la gráfica están conectados. Los elementos
     * deben estar en la gráfica.
     * @param a el primer elemento.
     * @param b el segundo elemento.
     * @return <code>true</code> si a y b son vecinos, <code>false</code> en otro caso.
     * @throws NoSuchElementException si a o b no son elementos de la gráfica.
     */
    public boolean sonVecinos(T a, T b) {
        // Aquí va su código.
		Vertice v = (Vertice) vertice(a);
		Vertice u = (Vertice) vertice(b);
		return v.vecinos.contiene(u) && u.vecinos.contiene(v);
    }

    /**
     * Regresa el vértice correspondiente el elemento recibido.
     * @param elemento el elemento del que queremos el vértice.
     * @throws NoSuchElementException si elemento no es elemento de la gráfica.
     * @return el vértice correspondiente el elemento recibido.
     */
    public VerticeGrafica<T> vertice(T elemento) {
        // Aquí va su código.
		for (Vertice v : vertices)
            if (v.elemento.equals(elemento))
                return v;
        throw new NoSuchElementException("El elemento no está en la gráfica");
    }

    /**
     * Define el color del vértice recibido.
     * @param vertice el vértice al que queremos definirle el color.
     * @param color el nuevo color del vértice.
     * @throws IllegalArgumentException si el vértice no es válido.
     */
    public void setColor(VerticeGrafica<T> vertice, Color color) {
        // Aquí va su código.
		Vertice v = new Vertice(vertice.get());
		if (vertice.getClass() != v.getClass())
			throw new IllegalArgumentException("Introduciste un vértice no válido");
		v = (Vertice) vertice;
		v.color = color;
    }

    /**
     * Nos dice si la gráfica es conexa.
     * @return <code>true</code> si la gráfica es conexa, <code>false</code> en
     *         otro caso.
     */
    public boolean esConexa() {
        // Aquí va su código.
		Cola<Vertice> colita = new Cola<>();
		Vertice w = vertices.getPrimero();
		for (Vertice v : vertices)
			v.color = Color.NINGUNO;
		w.color = Color.NEGRO;
		colita.mete(w);
		while (!colita.esVacia()) {
			Vertice u = (Vertice) colita.saca();
			for (Vertice vecino : u.vecinos) {
				if (vecino.color == Color.NINGUNO) {
					vecino.color = Color.NEGRO;
					colita.mete(vecino);
				}
			}
			u.color = Color.ROJO;
		}
		for (Vertice v : vertices)
			if (v.color != Color.ROJO)
				return false;
		return true;
    }

    /**
     * Realiza la acción recibida en cada uno de los vértices de la gráfica, en
     * el orden en que fueron agregados.
     * @param accion la acción a realizar.
     */
    public void paraCadaVertice(AccionVerticeGrafica<T> accion) {
        // Aquí va su código.
		for (Vertice v : vertices)
			accion.actua(v);
    }

    /**
     * Realiza la acción recibida en todos los vértices de la gráfica, en el
     * orden determinado por BFS, comenzando por el vértice correspondiente al
     * elemento recibido. Al terminar el método, todos los vértices tendrán
     * color {@link Color#NINGUNO}.
     * @param elemento el elemento sobre cuyo vértice queremos comenzar el
     *        recorrido.
     * @param accion la acción a realizar.
     * @throws NoSuchElementException si el elemento no está en la gráfica.
     */
    public void bfs(T elemento, AccionVerticeGrafica<T> accion) {
        // Aquí va su código.
		Cola<Vertice> colita = new Cola<>();
		recorre(elemento, colita, accion);
    }

	/**
	* Realiza la acción recibida en todos los vértices de la gráfica, en el
	* orden determinado por DFS, comenzando por el vértice correspondiente al
	* elemento recibido. Al terminar el método, todos los vértices tendrán
	* color {@link Color#NINGUNO}.
	* @param elemento el elemento sobre cuyo vértice queremos comenzar el
	*        recorrido.
	* @param accion la acción a realizar.
	* @throws NoSuchElementException si el elemento no está en la gráfica.
	*/
	public void dfs(T elemento, AccionVerticeGrafica<T> accion) {
		// Aquí va su código.
		Pila<Vertice> pilita = new Pila<>();
		recorre(elemento, pilita, accion);
	}

	/**
	* Realiza la acción recibida en todos los vértices de la gráfica, en el
	* orden determinado por la instancia de MeteSaca que recibe, comenzando por el vértice
	* correspondiente al elemento recibido.
	* Al terminar el método, todos los vértices tendrán
	* color {@link Color#NINGUNO}.
	* Si se recibe una Cola el orden es BFS
	* Si se recibe una Pila el orden es DFS
	* @param elemento el elemento sobre cuyo vértice queremos comenzar el
	*        recorrido.
	* @param instancia La instancia de la clase MeteSaca que nos indica
	*        el orden a seguir
	* @param accion la acción a realizar.
	* @throws NoSuchElementException si el elemento no está en la gráfica.
	*/
	private void recorre(T elemento, MeteSaca<Vertice> instancia, AccionVerticeGrafica<T> accion) {
		Vertice w = (Vertice) vertice(elemento);
		for (Vertice vecino : w.vecinos)
			vecino.color = Color.ROJO;
		w.color = Color.NEGRO;
		instancia.mete(w);
		while (!instancia.esVacia()) {
			Vertice u = (Vertice) instancia.saca();
			accion.actua(u);
			for (Vertice v : u.vecinos) {
				if (v.color == Color.ROJO) {
					v.color = Color.NEGRO;
					instancia.mete(v);
				}
			}
			u.color = Color.NINGUNO;
		}
	}


    /**
     * Nos dice si la gráfica es vacía.
     * @return <code>true</code> si la gráfica es vacía, <code>false</code> en
     *         otro caso.
     */
    @Override public boolean esVacia() {
        // Aquí va su código.
		return vertices.esVacia();
    }

    /**
     * Limpia la gráfica de vértices y aristas, dejándola vacía.
     */
    @Override public void limpia() {
        // Aquí va su código.
		vertices.limpia();
		aristas = 0;
    }

    /**
     * Regresa una representación en cadena de la gráfica.
     * @return una representación en cadena de la gráfica.
     */
    @Override public String toString() {
        // Aquí va su código.
		String vertex = "{";
		String ultima = "{";
		Lista<Vertice> temp = new Lista<>();
		/* Vertices */
		for (Vertice v : vertices)
			vertex += v.elemento.toString() + ", ";
		vertex += "}, ";
		/* Aristas */
		for (Vertice u : vertices){
			temp.agrega(u);
			for (Vertice v : u.vecinos){
				if (!temp.contiene(v))
					ultima += "(" + u.elemento.toString() + ", " + v.elemento.toString() + "), ";
			}
		}
		return vertex + ultima + "}";
    }

    /**
     * Nos dice si la gráfica es igual al objeto recibido.
     * @param objeto el objeto con el que hay que comparar.
     * @return <code>true</code> si la gráfica es igual al objeto recibido;
     *         <code>false</code> en otro caso.
     */
    @Override public boolean equals(Object objeto) {
        if (objeto == null || getClass() != objeto.getClass())
            return false;
        @SuppressWarnings("unchecked") Grafica<T> grafica = (Grafica<T>)objeto;
        // Aquí va su código.
		if (aristas != grafica.getAristas())
			return false;
		if (getElementos() != grafica.getElementos())
			return false;
		/* Checamos los vertices */
		for (Vertice v : grafica.vertices)
			if (!contiene(v.elemento))
				return false;
		/*Vamos con las aristas */
		for (Vertice propio : vertices) {
			for (Vertice vecino : propio.vecinos) {
				if (!grafica.sonVecinos(propio.elemento, vecino.elemento))
					return false;
			}
		}
		return true;
    }

    /**
     * Regresa un iterador para iterar la gráfica. La gráfica se itera en el
     * orden en que fueron agregados sus elementos.
     * @return un iterador para iterar la gráfica.
     */
    @Override public Iterator<T> iterator() {
        return new Iterador();
    }
}
