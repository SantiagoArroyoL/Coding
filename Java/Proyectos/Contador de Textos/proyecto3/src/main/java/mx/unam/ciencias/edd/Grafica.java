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
            // Aquí va su código.
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
    private class Vertice implements VerticeGrafica<T>, ComparableIndexable<Vertice> {

        /* El elemento del vértice. */
        public T elemento;
        /* El color del vértice. */
        public Color color;
        /* La distancia del vértice. */
        public double distancia;
        /* El índice del vértice. */
        public int indice;
        /* El diccionario de vecinos del vértice. */
        public Diccionario<T, Vecino> vecinos;

        /* Crea un nuevo vértice a partir de un elemento. */
        public Vertice(T elemento) {
            // Aquí va su código.
			this.elemento = elemento;
			color = Color.NINGUNO;
			vecinos = new Diccionario<>();
        }

        /* Regresa el elemento del vértice. */
        @Override public T get() {
            // Aquí va su código.
			return elemento;
        }

        /* Regresa el grado del vértice. */
        @Override public int getGrado() {
            // Aquí va su código.
			return vecinos.getElementos();
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

        /* Define el índice del vértice. */
        @Override public void setIndice(int indice) {
            // Aquí va su código.
			this.indice = indice;
        }

        /* Regresa el índice del vértice. */
        @Override public int getIndice() {
            // Aquí va su código.
			return indice;
        }

        /* Compara dos vértices por distancia. */
        @Override public int compareTo(Vertice vertice) {
            // Aquí va su código.
			if (vertice.distancia == -1)
				return -1;
			if (distancia - vertice.distancia < 0.0)
	            return -1;
	        if (distancia - vertice.distancia > 0.0)
	            return 1;
	        return 0;
        }
    }

    /* Clase interna privada para vértices vecinos. */
    private class Vecino implements VerticeGrafica<T> {

        /* El vértice vecino. */
        public Vertice vecino;
        /* El peso de la arista conectando al vértice con su vértice vecino. */
        public double peso;

        /* Construye un nuevo vecino con el vértice recibido como vecino y el
         * peso especificado. */
        public Vecino(Vertice vecino, double peso) {
            // Aquí va su código.
			this.vecino = vecino;
			this.peso = peso;
        }

        /* Regresa el elemento del vecino. */
        @Override public T get() {
            // Aquí va su código.
			return vecino.elemento;
        }

        /* Regresa el grado del vecino. */
        @Override public int getGrado() {
            // Aquí va su código.
			return vecino.getGrado();
        }

        /* Regresa el color del vecino. */
        @Override public Color getColor() {
            // Aquí va su código.
			return vecino.getColor();
        }

        /* Regresa un iterable para los vecinos del vecino. */
        @Override public Iterable<? extends VerticeGrafica<T>> vecinos() {
            // Aquí va su código.
			return vecino.vecinos();
        }
    }

    /* Interface para poder usar lambdas al buscar el elemento que sigue al
     * reconstruir un camino. */
    @FunctionalInterface
    private interface BuscadorCamino {
        /* Regresa true si el vértice se sigue del vecino. */
        public boolean seSiguen(Grafica.Vertice v, Grafica.Vecino a);
    }

    /* Vértices. */
    private Diccionario<T, Vertice> vertices;
    /* Número de aristas. */
    private int aristas;

    /**
     * Constructor único.
     */
    public Grafica() {
        // Aquí va su código.
		vertices = new Diccionario<>();
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
     * @throws IllegalArgumentException si el elemento ya había sido agregado a
     *         la gráfica.
     */
    @Override public void agrega(T elemento) {
        // Aquí va su código.
		if (elemento == null || contiene(elemento))
			throw new IllegalArgumentException("El elemento a agregar es nulo o ya esta en la gráfica");
		vertices.agrega(elemento,new Vertice(elemento));
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
		Vecino uVecino = new Vecino(u,1);
		Vecino vVecino = new Vecino(v,1);
		v.vecinos.agrega(b,uVecino);
		u.vecinos.agrega(a,vVecino);
    }

    /**
     * Conecta dos elementos de la gráfica. Los elementos deben estar en la
     * gráfica.
     * @param a el primer elemento a conectar.
     * @param b el segundo elemento a conectar.
     * @param peso el peso de la nueva vecino.
     * @throws NoSuchElementException si a o b no son elementos de la gráfica.
     * @throws IllegalArgumentException si a o b ya están conectados, si a es
     *         igual a b, o si el peso es no positivo.
     */
    public void conecta(T a, T b, double peso) {
        // Aquí va su código.
		if (a.equals(b) || sonVecinos(a,b))
			throw new IllegalArgumentException("Ambos elementos son iguales o ya son vecinos");
		if (peso <= 0)
			throw new IllegalArgumentException("El peso es menor o igual a cero");
		Vertice v = (Vertice) vertice(a);
		Vertice u = (Vertice) vertice(b);
		aristas++;
		Vecino uVecino = new Vecino(u,peso);
		Vecino vVecino = new Vecino(v,peso);
		v.vecinos.agrega(b,uVecino);
		u.vecinos.agrega(a,vVecino);
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
		v.vecinos.elimina(b);
		u.vecinos.elimina(a);
    }

    /**
     * Nos dice si el elemento está contenido en la gráfica.
     * @return <code>true</code> si el elemento está contenido en la gráfica,
     *         <code>false</code> en otro caso.
     */
    @Override public boolean contiene(T elemento) {
        // Aquí va su código.
		for (Vertice v : vertices)
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
		vertices.elimina(elemento);
		for (Vecino u : v.vecinos) {
			aristas--;
			u.vecino.vecinos.elimina(elemento);
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
		if(!contiene(a) || !contiene(b))
			throw new NoSuchElementException("Un vertice introducido no está en la gráfica");
		Vertice v = (Vertice) vertice(a);
		try {
			Vecino vVecino = vecino(v,b);
		} catch (NoSuchElementException nsee) {
			return false;
		}
		return true;
    }

    /**
     * Regresa el peso de la arista que comparten los vértices que contienen a
     * los elementos recibidos.
     * @param a el primer elemento.
     * @param b el segundo elemento.
     * @return el peso de la arista que comparten los vértices que contienen a
     *         los elementos recibidos.
     * @throws NoSuchElementException si a o b no son elementos de la gráfica.
     * @throws IllegalArgumentException si a o b no están conectados.
     */
    public double getPeso(T a, T b) {
        // Aquí va su código.
		if (!contiene(a) || !contiene(b))
			throw new NoSuchElementException("Los elementos no están en la gráfica");
		if (!sonVecinos(a,b))
			throw new IllegalArgumentException("Los elementos no son vecinos");
		Vertice v = (Vertice) vertice(a);
		Vecino vecino = vecino(v,b);
		return vecino.peso;
    }

    /**
     * Define el peso de la arista que comparten los vértices que contienen a
     * los elementos recibidos.
     * @param a el primer elemento.
     * @param b el segundo elemento.
     * @param peso el nuevo peso de la arista que comparten los vértices que
     *        contienen a los elementos recibidos.
     * @throws NoSuchElementException si a o b no son elementos de la gráfica.
     * @throws IllegalArgumentException si a o b no están conectados, o si peso
     *         es menor o igual que cero.
     */
    public void setPeso(T a, T b, double peso) {
        // Aquí va su código.
		if (peso <= 0)
			throw new IllegalArgumentException("El peso es menor o igual a cero");
		Vertice v = (Vertice) vertice(a);
		Vertice u = (Vertice) vertice(b);
		Vecino vVecino = vecino(u,a);
		Vecino uVecino = vecino(v,b);
		vVecino.peso = peso;
		uVecino.peso = peso;
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
     * Regresa el vértice vecino correspondiente a el vertice y elementos recibidos.
     * @param vertice el vertice del que queremos el vecino.
	 * @param elemento el elemento del vecino a encontrar.
     * @throws NoSuchElementException si elemento no es vecino de el vertice de la gráfica.
     * @return el vértice vecino correspondiente a el elemento recibido.
     */
    private Vecino vecino(Vertice vertice, T elemento) {
        // Aquí va su código.
		for (Vecino v : vertice.vecinos)
            if (v.get().equals(elemento))
                return v;
        throw new NoSuchElementException("No se encontró el vecino del vertice recibido");
    }

    /**
     * Define el color del vértice recibido.
     * @param vertice el vértice al que queremos definirle el color.
     * @param color el nuevo color del vértice.
     * @throws IllegalArgumentException si el vértice no es válido.
     */
    public void setColor(VerticeGrafica<T> vertice, Color color) {
        // Aquí va su código.
		if (vertice == null || (vertice.getClass() != Vertice.class && vertice.getClass() != Vecino.class))
			throw new IllegalArgumentException("Vertice inválido");
		if (vertice.getClass() == Vertice.class) {
			Vertice v = (Vertice) vertice;
			v.color = color;
		}
		if (vertice.getClass() == Vecino.class) {
			Vecino v = (Vecino) vertice;
			v.vecino.color = color;
		}
    }

    /**
     * Nos dice si la gráfica es conexa.
     * @return <code>true</code> si la gráfica es conexa, <code>false</code> en
     *         otro caso.
     */
    public boolean esConexa() {
        // Aquí va su código.
		Cola<Vertice> colita = new Cola<>();
		Iterator<Vertice> i = vertices.iterator();
		Vertice w = i.next();
		for (Vertice v : vertices)
			v.color = Color.NINGUNO;
		w.color = Color.NEGRO;
		colita.mete(w);
		while (!colita.esVacia()) {
			Vertice u = (Vertice) colita.saca();
			for (Vecino vc : u.vecinos) {
				if (vc.vecino.color == Color.NINGUNO) {
					vc.vecino.color = Color.NEGRO;
					colita.mete(vc.vecino);
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
		for (Vecino vc : w.vecinos)
			vc.vecino.color = Color.ROJO;
		w.color = Color.NEGRO;
		instancia.mete(w);
		while (!instancia.esVacia()) {
			Vertice u = (Vertice) instancia.saca();
			accion.actua(u);
			for (Vecino v : u.vecinos) {
				if (v.vecino.color == Color.ROJO) {
					v.vecino.color = Color.NEGRO;
					instancia.mete(v.vecino);
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
		for (Vertice u : vertices) {
			temp.agrega(u);
			for (Vecino v : u.vecinos) {
				if (!temp.contiene(v.vecino))
					ultima += "(" + u.elemento.toString() + ", " + v.vecino.elemento.toString() + "), ";
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
			for (Vecino vc : propio.vecinos) {
				if (!grafica.sonVecinos(propio.elemento, vc.get()))
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

    /**
     * Calcula una trayectoria de distancia mínima entre dos vértices.
     * @param origen el vértice de origen.
     * @param destino el vértice de destino.
     * @return Una lista con vértices de la gráfica, tal que forman una
     *         trayectoria de distancia mínima entre los vértices <code>a</code> y
     *         <code>b</code>. Si los elementos se encuentran en componentes conexos
     *         distintos, el algoritmo regresa una lista vacía.
     * @throws NoSuchElementException si alguno de los dos elementos no está en
     *         la gráfica.
     */
    public Lista<VerticeGrafica<T>> trayectoriaMinima(T origen, T destino) {
        // Aquí va su código.
		Vertice s = (Vertice) vertice(origen);
		Vertice t = (Vertice) vertice(destino);
		if (s == t) {
			Lista<VerticeGrafica<T>> trayectoria = new Lista<>();
			trayectoria.agrega(s);
			return trayectoria;
		}
		for (Vertice v : vertices)
			v.distancia = -1;
		Cola<Vertice> colita = new Cola<>();
		s.distancia = 0;
		colita.mete(s);
		while (!colita.esVacia()) {
			Vertice u = colita.saca();
			for (Vecino v : u.vecinos) {
				if (v.vecino.distancia == -1) {
					v.vecino.distancia = u.distancia+1;
					colita.mete(v.vecino);
				}
			}
		}
		if (t.distancia == -1)
			return new Lista<VerticeGrafica<T>>();
		return busquemosCamino(t,s,(u,v) -> {
			return v.vecino.distancia == u.distancia-1;
		});
    }

    /**
     * Calcula la ruta de peso mínimo entre el elemento de origen y el elemento
     * de destino.
     * @param origen el vértice origen.
     * @param destino el vértice destino.
     * @return una trayectoria de peso mínimo entre el vértice <code>origen</code> y
     *         el vértice <code>destino</code>. Si los vértices están en componentes
     *         conexas distintas, regresa una lista vacía.
     * @throws NoSuchElementException si alguno de los dos elementos no está en
     *         la gráfica.
     */
    public Lista<VerticeGrafica<T>> dijkstra(T origen, T destino) {
        // Aquí va su código.
		Vertice s = (Vertice) vertice(origen);
		Vertice t = (Vertice) vertice(destino);
		/* Usamos el infinito porque con -1 este no funcionó */
		for (Vertice v : vertices)
			v.distancia = Double.POSITIVE_INFINITY;
		s.distancia = 0;
		MonticuloMinimo<Vertice> monticulo = new MonticuloMinimo<>(vertices,getElementos());
		MonticuloMinimo<Vertice> monty = new MonticuloMinimo<>(vertices,getElementos());
		while (!monty.esVacia()) {
			Vertice u = monty.elimina();
			for (Vecino v : u.vecinos) {
				if (v.vecino.distancia > u.distancia+v.peso) {
					v.vecino.distancia = u.distancia+v.peso;
					monty.reordena(v.vecino);
				}
			}
		}
		if (t.distancia == Double.POSITIVE_INFINITY)
			return new Lista<VerticeGrafica<T>>();
		return busquemosCamino(t,s,(u,v) -> {
			return u.distancia == v.vecino.distancia+v.peso;
		});
    }

	/**
	 * Método auxiliar que reconstruye la trayectoria en revera
	 * El método funciona para trayectoriaMinima y dijkstra
	 * Recibe la interfaz funcional  buscador camino, a la que crearemos una lambda dependiendo el método
	 * @param u El vertice destino
	 * @param orign El vertice origen
	 * @param bc La interfaz que define si se siguen o no dos vertices
	 * @return una trayectoria de peso mínimo entre el vértice <code>origen</code> y
     *         el vértice <code>u</code>.
	 */
	private Lista<VerticeGrafica<T>> busquemosCamino(Vertice u, Vertice origen, BuscadorCamino bc) {
		Lista<VerticeGrafica<T>> trayectoria = new Lista<>();
		trayectoria.agrega(u);
		while(u != origen) {
			for (Vecino vecino : u.vecinos) {
				Vertice v = vecino.vecino;
				if (bc.seSiguen(u,vecino)) {
					trayectoria.agrega(v);
					u = v;
				}
			}
		}
		return trayectoria.reversa();
	}
}
