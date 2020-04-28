package mx.unam.ciencias.edd.proyecto2;

import mx.unam.ciencias.edd.*;
import java.lang.Math;

/**
 * Proyecto 2: Graficador SVG

 * Esta clase es la encargada de generar el código XML para las estructuras de datos permitidas
 * Si se quiere graficar una clase que no es válida mandaremos error
 *
 * @author Arroyo Lozano Santiago
 * @version 1.0
 * @since 11/04/2020 - 28/04/2020.
 */
public class Graficador {

	/* Cadena que define con qué clase estamos trabajando */
	private String clase;

	/* Etiqueta para texto. */
	private final String TEXTO = Svg.TEXTO.getLinea();
	/* Etiqueta para línea. */
	private final String LINEA = Svg.LINEA.getLinea();
	/* Abre etiqueta svg. y gráfica */
	private final String INICIO = Svg.INICIO.getLinea();
	/* Cierra etiqueta g. */
	private final String CIERRA = Svg.CIERRA.getLinea();
	/* Etiqueta para conectar las estructuras lineales. */
	private final String FLECHA = Svg.FLECHA.getLinea();
	/* Etiqueta para círculo de árboles y gráficas */
	private final String CIRCULO = Svg.CIRCULO.getLinea();
	/* Linea rvitraria para Pilas */
	private final String POLYLINE = Svg.POLYLINE.getLinea();
	/* Etiqueta para rectángulos. */
	private final String RECTANGULO = Svg.RECTANGULO.getLinea();

	/**
	 * Constructor de nuestra clase Grafica
	 * @param clase String que define con qué clase estamos trabajando
	 */
	public Graficador(String clase) {
		this.clase = clase;
	}

	/**
	 * El método que revisa con qué clase estamos trabajando y con base en eso
	 * manda a llamar al método específico de cada clase
	 * Si se quiere graficar una clase que no es válida mandaremos error
	 * @param listaFinal La lista que contiene los elementos de la clase a graficar
	 * @return El código XML para dibujar el SVG de la coleccion
	 */
	public String graficaColeccion(Lista<Integer> listaFinal) {
		switch (clase) {
			case "Arreglos":
				return dibujaArreglo(listaFinal);
			case "Lista":
				return dibujaLista(listaFinal);
			case "ArbolAVL":
				return dibujaArbolBinario(new ArbolAVL<>(listaFinal));
			case "ArbolBinarioCompleto":
				return dibujaArbolBinario(new ArbolBinarioCompleto<>(listaFinal));
			case "ArbolBinarioOrdenado":
				return dibujaArbolBinario(new ArbolBinarioOrdenado<>(listaFinal));
			case "ArbolRojinegro":
				return dibujaArbolBinario(new ArbolRojinegro<>(listaFinal));
			case "Cola":
				return dibujaMeteSaca(listaFinal);
			case "Pila":
				return dibujaMeteSaca(listaFinal);
			case "Grafica":
				return dibujaGrafica(listaFinal);
			case "MonticuloMinimo":
				return dibujaMonticulo(listaFinal);
			default: {
				System.err.println("La clase introducida no es válida");
				System.exit(-1);
			}
		}//Cierre del switch
		return "";
	}

	/**
	 * Algoritmo que dibuja un arreglo
	 * Dibujaremos un arectángulo para cada elemento del arreglo
	 * @param listaFinal La lista que contiene los elementos del arreglo
	 * @return El código XML para dibujar el SVG de el arreglo
	 */
	private String dibujaArreglo(Lista<Integer> listaFinal) {
		int tamaño, i;
		tamaño = 50*listaFinal.getLongitud() + 10*listaFinal.getLongitud()-1;
		String dibujo = String.format(INICIO,tamaño+200,200,clase);
		/* Para cada elemento en el dibujo debemos crear el rectángulo
		El indice i nos ayudará para saber en qué rectangulo vamos */
		i = 1;
		for (int elemento : listaFinal) {
			dibujo += String.format(RECTANGULO,60*i,10,60,20);
			dibujo += String.format(TEXTO,60*i+30,26,"black",elemento);
			i++;
		}
		return dibujo + CIERRA;
	}

	/**
	 * Algoritmo que dibuja un arreglo
	 * Dibujaremos un rectángulo para cada elemento de la lista conetados por una doble flecha
	 * @param listaFinal La lista a graficar
	 * @return El código XML para dibujar el SVG de la lista
	 */
	private String dibujaLista(Lista<Integer> listaFinal) {
		int tamaño, i;
		tamaño = 50*listaFinal.getLongitud() + 10*listaFinal.getLongitud()-1;
		String dibujo = String.format(INICIO,tamaño+200,200,clase);
		/* Para cada elemento en el dibujo debemos crear el rectángulo
		El indice i nos ayudará para saber en qué rectangulo vamos */
		i = 1;
		for (int elemento : listaFinal) {
			dibujo += String.format(RECTANGULO,60*i,10,50,20);
			if (i+1 < listaFinal.getLongitud()+1)
				/* La etiqueta &#x2194 en XML se interpreta como una doble flecha */
				dibujo += String.format(FLECHA,10,60*(i+1)-5,20, "&#x2194;");
			dibujo += String.format(TEXTO,60*i+25,26,"black",elemento);
			i++;
		}
		return dibujo + CIERRA;
	}

	/**
	 * Algoritmo que dibuja una estructura de la clase MeteSaca<T>
	 * Sea una pila o una cola, utilizaremos una pila para dibujar.
	 * En el caso de la cola lo único que haremos es dibujar al revés.
	 * Como no podemos saber el tamaño de la estructura, primero recorremos la estructura
	 * y luego empezamos a dibujar, almacenando en una lista auxiliar las lineas de XML
	 * Los dibujos de ambas estructras están basados en cómo se presentan en el libro
	 * Estructuras de Datos con Java Moderno.
	 * @param listaFinal La lista que contiene los elementos de la estructura
	 * @return El código XML para dibujar el SVG de la estructura
	 */
	public String dibujaMeteSaca(Lista<Integer> listaFinal) {
		/* Creamos la pila a partir de la Lista */
		Pila<Integer> pilaFinal = new Pila<>();
		for (int i : listaFinal)
			pilaFinal.mete(i);
		int i = 0, x = 27;
		int alturaTotal = 500, anchuraTotal = 0;
		Lista<String> lineas = new Lista<String>();
		int anchura = 0;
		if (clase.equals("Pila")) {
			while (!pilaFinal.esVacia()) {
				int elemento = pilaFinal.saca();
				/* Definimos cuál es ellargo del número */
				if(String.valueOf(elemento).length() > anchuraTotal)
					anchuraTotal = String.valueOf(elemento).length();
				/* Si el número tiene mas de tres dígitos debemos hacer la pila más ancha */
				if (anchuraTotal > 3) {
					anchura = anchuraTotal*13+13;
					x = 30+anchuraTotal*3;
				} else {
					x = 27;
					anchura = 45;
				}
				lineas.agrega(String.format(TEXTO,x,(30*i)+35,"black",elemento));
				i++;
			}
			alturaTotal = 20*(i+1) + 10*i;
			String dibujo = String.format(INICIO,anchuraTotal*50,alturaTotal+30,clase);
			/* Con POLYLINE creamos la pila */
			dibujo += String.format(POLYLINE,alturaTotal,anchura,alturaTotal,anchura);
			/* Agregamos los elementos a la pila */
			for (String s : lineas)
				dibujo += s;
			dibujo += CIERRA;
			return dibujo;
		}
		i = 1;
		/* Agregamos el puro texto a la lista */
		while (!pilaFinal.esVacia()) {
			int elemento = pilaFinal.saca();
			lineas.agrega(String.format(TEXTO,(60*i)+25,25,"black",elemento));
			i++;
		}
		anchuraTotal = 50*i + 10*(i-1);
		String dibujo = String.format(INICIO,anchuraTotal+50,alturaTotal,clase);
		/* La etiqueta &#x2192 en XML se interpreta como una flecha a la derecha
		 * Como ya tenemos la anchuraTotal empezamos a dibujar */
		dibujo += String.format(FLECHA,30,55,25,"&#x2192;");
		dibujo += String.format(LINEA,60,5,anchuraTotal,5);
		for (String s : lineas)
			dibujo += s;
		dibujo += String.format(LINEA,60,30,anchuraTotal,30);
		dibujo += String.format(FLECHA,30,60*i-5,25,"&#x2192;");
		return dibujo + CIERRA;
	}


	/**
	* Dibuja un árbol binario de cualquier tipo.
	* Recorreremos todos los arboles por BFS (menos los binariosOrdenados)
	* @param arbol El arbol a graficar
	* La única razón por la que modificamos una instancia de MeteSaca es porque
	* los aroles binarios Ordenados los recorreremos por DFS, con una pila .
	* Al contrario de los demás árboles que usarán una cola
	* Esta limitación de losa rboles Ordenados impide que usemos la funciones lambda
	* y los métodos BFS o DFS ya implementados. Por lo que lo recorreremos manualmente
	* @return El código XML para dibujar el SVG de el arbol binario.
	*/
	public String dibujaArbolBinario(ArbolBinario<Integer> arbol) {
		MeteSaca<VerticeArbolBinario<Integer>> instancia;
		if (clase.equals("ArbolBinarioOrdenado"))
			instancia = new Pila<>();
		else
			instancia = new Cola<>();
		int y, a = arbol.altura();
		String dibujo = String.format(INICIO,a*550,a*126,clase);
		Lista<String> circulos = new Lista<String>();
		VerticeArbolBinario<Integer> v = arbol.raiz();
		Lista<VerticeArbolBinario<Integer>> vertices = new Lista<>();
		int[] padres = new int[arbol.getElementos()];
		int tempY = 100*v.profundidad()+30;
		int x = 150*v.altura()+250;
		/* Los arbolesBinariosOrdenados en general son más altos */
		if (clase.equals("ArbolBinarioOrdenado") && v.altura() > 6)
		    x = 50*v.altura()+80;
		int separacion = x+700;
		instancia.mete(v);
		while (!instancia.esVacia()) {
			VerticeArbolBinario<Integer> temp = instancia.saca();
			y = 100*temp.profundidad()+30;
			/* Si cambia de altura */
			if (y != tempY)	{
				separacion = separacion/2;
				tempY = y;
			}
			/* Decrementamos la separacion entre cada vertice */
			if (temp.hayPadre()) {
				int i = vertices.indiceDe(temp.padre());
				if(esDerecho(temp))
					x = padres[i]+separacion/2;
 				else
					x = padres[i]-separacion/2;
			}
			/* Checamos si es necesario recorrer y dibujar un hijo izquierdo */
			if (temp.hayIzquierdo()) {
				instancia.mete(temp.izquierdo());
				dibujo += String.format(LINEA,x,y,x-(separacion/2)/2,y+100);
			}
			/* Checamos si es necesario recorrer y dibujar un hijo derecho */
			if (temp.hayDerecho()) {
				instancia.mete(temp.derecho());
				dibujo += String.format(LINEA,x,y,x+(separacion/2)/2,y+100);
			}
			/* Si tiene al menos un hijo lo agregamos a la lista de padres */
			if (temp.hayDerecho() || temp.hayIzquierdo()){
				vertices.agrega(temp);
				padres[vertices.indiceDe(temp)] = x;
			}
			/* Dibujamos el vertice */
			if (clase.equals("ArbolRojinegro"))
				circulos.agrega(dibujaVerticeRojinegro(temp,x,y));
			else
				circulos.agrega(dibujaVertice(temp,x,y));
		}//Cierre del bucle while
		/* Para que las líneas no se empalmen con los circulos, dibujamos los vertices hasta el final */
		for (String str : circulos) {
			dibujo += str;
		}
		return dibujo + CIERRA;
	}

	/**
	 * Método auxiliar que dibuja el vértice recibido en las coordenadas x,y recibidas
	 * @param v El vertice de el Arbol a dibujar
	 * @param x El valor x donde va el vertice
	 * @param y El valor y donde va el vertice
	 * @return El codigo XML con el valor del dibujo de sólo este vértice
	 */
	private String dibujaVertice(VerticeArbolBinario<Integer> v, int x, int y) {
		String balance;
		String dibujoAux = String.format(CIRCULO,x,y,"white");
		dibujoAux += String.format(TEXTO,x,y+5,"black",v.get());
		/* Si es AVL de su ToString() Obtenemos el balance y lo dibujamos arriba del vértice */
		if (clase.equals("ArbolAVL")){
			String[] temp = v.toString().split(" ");
			balance = "[" + temp[1] + "]";
			if (esDerecho(v))
				dibujoAux += String.format(TEXTO,x+15,y-23,"black",balance);
			else if (!v.hayPadre())
				dibujoAux += String.format(TEXTO,x-35,y-15,"black",balance);
			else
				dibujoAux += String.format(TEXTO,x-15,y-23,"black",balance);
		}
		return dibujoAux;
	}

	/**
	 * Método auxiliar que gráfica el vértice recibido en las coordenadas x, y recibidas
	 * Este método es exlusivo para vertices Rojinegros, ya que basándonos en su
	 * @param v El vertice del arbol a dibujar
	 * @param x El valor x donde va el vertice
	 * @param y El valor y donde va el vertice
	 * @return El codigo XML con el valor del dibujo de sólo este vértice
	 */
	private String dibujaVerticeRojinegro(VerticeArbolBinario<Integer> v, int x, int y) {
		String color;
		ArbolRojinegro<Integer> a = new ArbolRojinegro<>();
		if  (a.getColor(v) == Color.ROJO)
			color = "red";
		else
			color = "black";
		String dibujoAux = "";
		dibujoAux += String.format(CIRCULO,x,y,color);
		dibujoAux += String.format(TEXTO,x,y+5,"white",v.get());
		return dibujoAux;
	}

	/**
	 * Método que nos indica si el hijo es derecho
	 * @param v El vertice a comparar
	 * @return true en caso de serlo, false en caso contrario
	 */
	private boolean esDerecho(VerticeArbolBinario<Integer> v) {
		//Comparamos con == puesto que deben ser la misma referencia
		if (!v.hayPadre())
			return false;
		VerticeArbolBinario<Integer> padre = v.padre();
		if (padre.hayDerecho()) {
			if (v.padre().derecho() == v)
				return true;
			else
				return false;
		} else {
			return false;
		}
    }

	/**
	 * Algoritmo auxiliar para dibujar gráficas en SVG.
	 * Construiremos una gráfica con los vértices y aristas recibidos en la lista (Sólo si esta es válida)
	 * Para no tener problema al constuir la gráfica cuando agreguemos el mismo vértice dos veces
	 * usaremos un try-catch:
	 * Aumentaría la complejidad si antes de agregar nos  aseguramos de que no contenga al vértice
	 * para no agregarlo 2 veces. Habría que recorrer la lista de vértices para ver si
	 * la grafica contiene cada vértice. Este error se dispara en los casos cuando el vértice
	 * está sólo o cuando se agrega un nuevo arista al mismo vértice
	 * Para que las graficas no se amontonen es necesario calcular el angulo
	 * que tendrán los vértices entre sí. Esto lo haremos con el máximo número de vértices
	 * Así tendremos un radio y un ángulo bien definido para cada vértice.
	 * Como el iterador de la gráfica realmente itera su lista interna de vertices usaremos
	 * el metodo paracadaVertice() con una lambda para recorrer de manera más óptima la Gráfica
	 * @param listaFinal La lista que contiene las parejas de vertices y aritas
	 * @return El código XML para dibujar el SVG de la gráfica.
	 */
	private String dibujaGrafica(Lista<Integer> listaFinal) {
		/* Creamos la gráfica. */
		int contador = 1, temp = 0;
		Grafica<Integer> g = new Grafica<>();
		for (int elemento : listaFinal) {
			try {
				g.agrega(elemento);
			} catch (IllegalArgumentException iae) {
				// No hacemos nada
			}
			/* Cada pareja de elementos debe tener un arista que los conecte entre sí  */
			if (contador % 2 == 0 && temp != elemento)
				g.conecta(temp, elemento);
			contador++;
			temp = elemento;
		}
		/* Empezamos a graficar. Como usaremos una lamda todas las variables que usemos
		 * deben ser de tipo final */
		final double angulo = 360 / g.getElementos();
    	final int radio = 40 * g.getElementos();
    	final int centro = radio + 25;
		final Lista<Integer> lista = new Lista<>();
		final Lista<String> lineas = new Lista<>();
		final int tamaño = g.getElementos()*250;
		/* Con este truquito sí podremos modificar el valor de ángulo dentro de la lambda */
		final double[] ang = {angulo};
		for (int i : g)
			lista.agrega(i);
		/* Al contrario de los árboles, aquí sí podemos hacer una lambda */
		g.paraCadaVertice((v) -> {

			/* Obtenemos los valores de X y Y */
			int x = calculaCoordenadaX(ang[0],radio);
			int y = calculaCoordenadaY(ang[0],radio);

			/* Graficamos los vecinos de v.(Para no dibujar dos veces la misma línea lo pintamos de rojo)*/
			for(VerticeGrafica<Integer> vecino : v.vecinos()){
				if(vecino.getColor() != Color.ROJO){
					int i = lista.indiceDe(vecino.get());
					int auxX = calculaCoordenadaX((i+1)*angulo,radio);
					int auxY = calculaCoordenadaY((i+1)*angulo,radio);
					lineas.agrega(String.format(LINEA,centro+x,centro-y,centro+auxX, centro-auxY));
				}
			}
			lineas.agrega(dibujaVertice(v,centro+x,centro-y));
			double auxAng = ang[0];
			auxAng += angulo;
			ang[0] = auxAng;
			g.setColor(v,Color.ROJO);
		}); //Cierre de paraCadaVertice
		String dibujo = String.format(INICIO,tamaño,tamaño,clase);
		for (String str : lineas) {
			dibujo += str;
		}
		return dibujo + CIERRA;
	}

	/**
	 * Método auxiliar que dibuja el vértice recibido en las coordenadas x,y recibidas
	 * @param v El vertice de la Gráfica a dibujar
	 * @param x El valor x donde va el vertice
	 * @param y El valor y donde va el vertice
	 * @return El codigo XML con el valor del dibujo de sólo este vértice
	 */
	private String dibujaVertice(VerticeGrafica<Integer> v, int x, int y) {
		String dibujoAux = String.format(CIRCULO,x,y,"white");
		dibujoAux += String.format(TEXTO,x,y+5,"black",v.get());
		return dibujoAux;
	}

	/**
    * Método auxiliar que calcula las coordenadas de los vértices basándose en
    * el ángulo que reciba. Se necesita mover en el eje X usando coseno (en radianes).
	* @param angulo El valor double del angulo
	* @param radio El radio máximo que pueden tener
    * @return la coordenada X.
	*/
	private int calculaCoordenadaX(double angulo, int radio){
		return (int) Math.floor(Math.cos(Math.toRadians(angulo)) * radio) ;
	}

	/**
	* Método auxiliar que calcula las coordenadas de los vértices basándose en
	* el ángulo que reciba. Se necesita mover en el eje Y usando seno (en radianes).
	* @param angulo El valor double del angulo
	* @param radio El radio máximo que pueden tener
	* @return la coordenada Y.
	*/
	private int calculaCoordenadaY(double angulo, int radio){
		return (int) Math.floor(Math.sin(Math.toRadians(angulo)) * radio);
	}

	/**
	 * Algoritmo auxiliar para dibujar Montículos en SVG.
	 * Como los enteros que recibimos en el archivo no implemetnaban Valor indexable,
	 * construiremos cada elemento y lo agregaremos a un nuevo montículo mínimo
	 * Si agregamos dos o más veces el mismo elemento cambiaremos el valor de su índice para mantener
	 * el orden y que no haya dos elementos exactamente iguales
	 * @param listaFinal La lista que contiene los enteros a modificar
	 * @return El código XML para dibujar el SVG de el montículo
	 */
	private String dibujaMonticulo(Lista<Integer> listaFinal) {
		MonticuloMinimo<ValorIndexable<Integer>> monty = new MonticuloMinimo<>();
		Cola<ValorIndexable<Integer>> colita = new Cola<>();
		Lista<ValorIndexable<Integer>> vertices = new Lista<>();
		int v = 0, tempEntero = 0, contador = 1;
		int y, elementos = listaFinal.getElementos();
		int[] padres = new int[elementos];
		int altura = getAlturaMonticulo(elementos);
		int x = 150*altura+250;
		int separacion = x+700;
		Lista<String> circulos = new Lista<>();
		String dibujo = String.format(INICIO,elementos*200,elementos*100,clase);
		/* Construimos el montículo */
		for (int i : listaFinal) {
			if (tempEntero == i) {
				v = i+contador;
				contador++;
			} else {
				v = i;
			}
			monty.agrega(new ValorIndexable<Integer>(i,v));
			tempEntero = i;
		}
		/* -Vamos a recorrer el montículo por VFS usando una cola */
		colita.mete(monty.get(0));
		int tempY = 100*getPiso(monty.get(0), monty)+30;
		while (!colita.esVacia()) {
			ValorIndexable<Integer> temp = colita.saca();
			int index = temp.getIndice();
			int padre = getPadre(temp);
			y = 100*getPiso(temp, monty)+30;
			/* Si cambia de altura */
			if (y != tempY)	{
				separacion = separacion/2;
				tempY = y;
			}
			/* Decrementamos la separacion entre cada vertice */
			if (padre >= 0) {
				int i = vertices.indiceDe(monty.get(padre));
				if(getDerecho(monty.get(padre)) == index)
					x = padres[i]+separacion/2;
 				else
					x = padres[i]-separacion/2;
			}
			/* Checamos si es necesario recorrer y dibujar un hijo izquierdo */
			int izq = getIzquierdo(temp);
			int der = getDerecho(temp);
			if (izq < elementos) {
				colita.mete(monty.get(izq));
				dibujo += String.format(LINEA,x,y,x-(separacion/2)/2,y+100);
			}
			/* Checamos si es necesario recorrer y dibujar un hijo derecho */
			if (der < elementos) {
				colita.mete(monty.get(der));
				dibujo += String.format(LINEA,x,y,x+(separacion/2)/2,y+100);
			}
			/* Si tiene al menos un hijo lo agregamos a la lista de padres */
			if (der < elementos || izq < elementos){
				vertices.agrega(temp);
				padres[vertices.indiceDe(temp)] = x;
			}
			/* Dibujamos el vertice */
			circulos.agrega(dibujaVertice(temp,x,y));
		}//Cierre del bucle while
		/* Para que las líneas no se empalmen con los circulos, dibujamos los vertices hasta el final */
		for (String str : circulos) {
			dibujo += str;
		}
		return dibujo + CIERRA;
	}

	/**
	 * Método auxiliar que dibuja el vértice recibido en las coordenadas x,y recibidas
	 * @param elemento El elemento del vertice de el Montículo a dibujar
	 * @param x El valor x donde va el vertice
	 * @param y El valor y donde va el vertice
	 * @return El codigo XML con el valor del dibujo de sólo este vértice
	 */
	private String dibujaVertice(ValorIndexable<Integer> elemento, int x, int y) {
		String[] temp = elemento.toString().split(":");
		String dibujoAux = String.format(CIRCULO,x,y,"white");
		dibujoAux += String.format(TEXTO,x,y+5,"black",temp[0]);
		return dibujoAux;
	}

	/**
	 * Método que regresa el índice del hijo izquierdo de un elemento de un montículo mínimo
	 * @param elemento El elemento del cual queremos su hijo izquierdo
	 * @return El índice de dónde se encuentra el hijo izquierdo en el Montículo
	 */
	private int getIzquierdo(ValorIndexable<Integer> elemento) {
		int i = elemento.getIndice();
		return 2*i+1;
	}

	/**
	 * Método que regresa el índice del hijo derecho de un elemento de un montículo mínimo
	 * @param elemento El elemento del cual queremos su hijo derecho
	 * @return El índice de dónde se encuentra el hijo derecho en el Montículo
	 */
	private int getDerecho(ValorIndexable<Integer> elemento) {
		int i = elemento.getIndice();
		return 2*i+2;
	}

	/**
	 * Método auxiliar que nos da el índice del padre de algún vértice de un montículo mínimo
	 * @param elemento El elemento del vértice hijo
	 * @return el indice de su padre
	 */
	private int getPadre(ValorIndexable<Integer> elemento) {
		int i = elemento.getIndice();
		if (i == 0)
			return -1;
		return (int) Math.floor((i-1)/2);
	}

	/**
	 * Método auxiliar para calcular la altura de un montículo mínimo
	 * (También podría calcular la altura de un arbol binario completo)
	 * Básicamente este método calcula el piso de logaritmo base 2 de un entero x
	 * @param x El número entero a calcular
	 * @return El piso del logaritmo base 2 del entero recibido
	 */
	private int getAlturaMonticulo(int x) {
    	return (int) Math.floor(Math.log(x) / Math.log(2));
	}

	/**
	 * Método que regresa la profundidad de un vértice de un Montículo Mínimo
	 * @param elemento El elemento del cual queremos saber en qué piso está (profundidad)
	 * @param monty El montículo mínimo que contiene al elemento
	 * @return Un número entero positivo que indica en qué piso está (que profundidad tiene) el vértice
	 */
	private int getPiso(ValorIndexable<Integer> elemento, MonticuloMinimo<ValorIndexable<Integer>> monty) {
		int i = elemento.getIndice();
		int padre = getPadre(elemento);
		if (i == 0)
			return 0;
		return getPiso(monty.get(padre) , monty) + 1;
	}

}//Cierre de la clase Grafica
