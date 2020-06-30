package mx.unam.ciencias.edd.proyecto3;

import java.lang.Math;
import java.util.Iterator;
import mx.unam.ciencias.edd.*;

/**
 * Proyecto 3: Ordenador de textos

 * Esta clase es la encargada de generar el código XML para las estructuras de datos permitidas
 * Si se quiere graficar una clase que no es válida mandaremos error
 * Esta clase también cuenta el total de palabras en todo un arhivo, NO cuántas veces se repite cada palabra,
 * sólo el total del archivo.
 *
 * @author Arroyo Lozano Santiago
 * @version 2.0
 * @since 23/05/2020 - 12/06/2020
 */
public class Graficador {

	/**
	 * Clase interna privada encargada de proporcionar una manera más sencilla de comparar
	 * dos cadenas basandonos sólo en cuántas veces se repite esta en un archivo
	 */
	private class Rengloncillo implements Comparable<Rengloncillo> {

		/* La palabra */
		public String elemento;
		/* Cuántas veces se repite */
		public int valor;

		/**
		 * Constructor de Rengloncillo
		 * @param elemento La cadena que tendrá el Rengloncillo
		 * @param valor El número entero que indica cuantás veces se repite
		 */
		public Rengloncillo(String elemento, int valor) {
			this.elemento = elemento;
			this.valor = valor;
		}

		/**
		 * Método que regresa la cantidad de veces que se repite la palabra
		 */
		public int valor() {
			return valor;
		}

		/**
		 * Regresa una representación en cadena del Rengloncillo
		 * @return una representación en cadena del Rengloncillo
		 */
		@Override public String toString() {
			return elemento;
		}

		/**
		 * Método que compara este renglón con otra instancia de la misma clase
		 * @param r El otro renglón a comparar
		 * @return un valor menor que cero si el rengloncillo que llama el método
		 *         es menor que el parámetro; cero si son iguales; o mayor que cero
		 *         si es mayor.
		 */
		@Override public int compareTo(Rengloncillo r) {
	        return valor - r.valor;
		}

	}//Cierre de la clase Rengloncillo

	/* Cadena que define con qué clase estamos trabajando */
	private String clase;
	/* Contador */
	private int cont = 0;
	/* Lista de todos las palabras procesadas por la clase */
	private Lista<Rengloncillo> comunes = new Lista<>();
	/* Arreglo de cadenas, que contiene los colores que usaremos en las gráficas */
	private final String[] colores = new String[]{"yellow","green","blue","orange","purple"};

	/* Cerramos la etiqueta head de html */
	private final String HEAD = Svg.HEAD.getLinea();
	/* Etiqueta para texto. */
	private final String TEXTO = Svg.TEXTO.getLinea();
	/* Etiqueta para línea. */
	private final String LINEA = Svg.LINEA.getLinea();
	/* Indexamos un archivo html externo a index.html*/
	private final String INDEX = Svg.INDEX.getLinea();
	/* Un rectángulo que usareos exlusivamete para la gráfica de barras */
	private final String BARRA = Svg.BARRA.getLinea();
	/* Abre etiqueta svg. y gráfica */
	private final String INICIO = Svg.INICIO.getLinea();
	/* Cierra etiqueta g. */
	private final String CIERRA = Svg.CIERRA.getLinea();
	/* Etiqueta para conectar las estructuras lineales*/
	private final String FLECHA = Svg.FLECHA.getLinea();
	/* Abrimos la etiqueta g */
	private final String ABRE_G = Svg.ABRE_G.getLinea();
	/* Espacio en la etiqueta head para importar estilos de css */
	private final String ESTILO = Svg.ESTILO.getLinea();
	/* Título de la gráffica de barras en xml */
	private final String TITULO = Svg.TITULO.getLinea();
	/* Etiqueta xml que genera un svg amplio para la gráfica de pastel */
	private final String PASTEL = Svg.PASTEL.getLinea();
	/* Etiqueta para círculo de árboles y gráficas */
	private final String CIRCULO = Svg.CIRCULO.getLinea();
	/* Linea arbitraria para Pilas */
	private final String POLYLINE = Svg.POLYLINE.getLinea();
	/* Cerramos la etiqueta g */
	private final String CIERRA_G = Svg.CIERRA_G.getLinea();
	/* Etiqueta para circulo de árboles con radio */
	private final String CIRCULO_R = Svg.CIRCULO_R.getLinea();
	/* Etiqueta para rectángulos. */
	private final String RECTANGULO = Svg.RECTANGULO.getLinea();
	/* Cerramos la etiqueta svg */
	private final String CIERRA_SVG = Svg.CIERRA_SVG.getLinea();
	/* Cerramos el código HTML */
	private final String FINAL_HTML = Svg.FINAL_HTML.getLinea();
	/* El texto de la gráfica de barras */
	private final String TEXTO_BARRA = Svg.TEXTO_BARRA.getLinea();
	/* Creamos un archivo HTML con todo lo necesario */
	private final String INICIO_HTML = Svg.INICIO_HTML.getLinea();
	/* Creamos un archivo html con todo lo necesario para el index */
	private final String INICIO_INDEX = Svg.INICIO_INDEX.getLinea();
	/* Etiqueta que crea el xml necesario para la gráfica de arras */
	private final String INICIO_BARRA = Svg.INICIO_BARRA.getLinea();
	/* Etiqueta de cada gajo de la gráfica de pastel */
	private final String PASTEL_INICIO = Svg.PASTEL_INICIO.getLinea();

	/**
	 * Constructor de nuestra clase Grafica
	 * @param clase String que define con qué clase estamos trabajando
	 */
	public Graficador(String clase) {
		this.clase = clase;
	}

	/**
	* Dibuja un árbol binario de cualquier tipo.
	* Recorreremos todos los arboles por BFS (menos los binariosOrdenados)
	* La única razón por la que modificamos una instancia de MeteSaca es porque
	* los aroles binarios Ordenados los recorreremos por DFS, con una pila .
	* Al contrario de los demás árboles que usarán una cola
	* Esta limitación de losa rboles Ordenados impide que usemos la funciones lambda
	* y los métodos BFS o DFS ya implementados. Por lo que lo recorreremos manualmente
	* @param arbol El arbol a graficar
	* @return El código XML para dibujar el SVG de el arbol binario.
	*/
	public String dibujaArbolBinario(ArbolBinario<Rengloncillo> arbol) {
		MeteSaca<VerticeArbolBinario<Rengloncillo>> instancia;
		if (clase.equals("ArbolBinarioOrdenado"))
			instancia = new Pila<>();
		else
			instancia = new Cola<>();
		String dibujo;
		int y, a = arbol.altura();
		Lista<String> circulos = new Lista<String>();
		VerticeArbolBinario<Rengloncillo> v = arbol.raiz();
		Lista<VerticeArbolBinario<Rengloncillo>> vertices = new Lista<>();
		int[] padres = new int[arbol.getElementos()];
		int tempY = 100*v.profundidad()+30;
		int x = 150*v.altura()+250;
		if (arbol.getElementos() <= 3)
			dibujo = String.format(INICIO,750,550,clase);
		else
			dibujo = String.format(INICIO,a*550,a*126,clase);
		/* Los arbolesBinariosOrdenados en general son más altos */
		if (clase.equals("ArbolBinarioOrdenado") && v.altura() > 6)
		    x = 50*v.altura()+80;
		int separacion = x+700;
		instancia.mete(v);
		while (!instancia.esVacia()) {
			VerticeArbolBinario<Rengloncillo> temp = instancia.saca();
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
	private String dibujaVertice(VerticeArbolBinario<Rengloncillo> v, int x, int y) {
		String balance;
		String dibujoAux;
		int n = v.get().toString().length();
		if (n > 5) {
			dibujoAux = String.format(CIRCULO_R,x,y+16,n+30,"white");
			dibujoAux += String.format(TEXTO,x,y+21,"black",v.get());
		} else {
			dibujoAux = String.format(CIRCULO,x,y,"white");
			dibujoAux += String.format(TEXTO,x,y+5,"black",v.get());
		}
		/* Si es AVL de su ToString() Obtenemos el balance y lo dibujamos arriba del vértice */
		if (clase.equals("ArbolAVL")) {
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
	private String dibujaVerticeRojinegro(VerticeArbolBinario<Rengloncillo> v, int x, int y) {
		String color;
		ArbolRojinegro<Rengloncillo> a = new ArbolRojinegro<>();
		if  (a.getColor(v) == Color.ROJO)
			color = "red";
		else
			color = "black";
		String dibujoAux = "";
		int n = v.get().toString().length();
		if (n > 5)
			dibujoAux += String.format(CIRCULO_R,x,y,(n+30),color);
		else
			dibujoAux += String.format(CIRCULO,x,y,color);
		dibujoAux += String.format(TEXTO,x,y+5,"white",v.get());
		return dibujoAux;
	}

	/**
	 * Método que nos indica si el hijo es derecho
	 * @param v El vertice a comparar
	 * @return true en caso de serlo, false en caso contrario
	 */
	private boolean esDerecho(VerticeArbolBinario<Rengloncillo> v) {
		//Comparamos con == puesto que deben ser la misma referencia
		if (!v.hayPadre())
			return false;
		VerticeArbolBinario<Rengloncillo> padre = v.padre();
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
		/* Revisamos que la lista tenga número par de elementos*/
		if (listaFinal.getElementos() % 2 != 0) {
			System.err.println("Por favor introduce un número par de elementos");
			System.exit(-1);
		}
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
			try {
				if (contador % 2 == 0 && temp != elemento)
				g.conecta(temp, elemento);
			} catch (IllegalArgumentException iae) {
				// No hacemos nada
			}
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
	 * Algoritmo que dibuja un archivo html, con una gráfica de barras, una gráfica de pastel,
	 * un ArbolRojinegro y un ArbolAVL. Estos conteniendo las palabras más usadas
	 * en e ldiccionario recibido
	 * @param d Un diccionario cuyas llaves son las palabras del archivo y su valor es
	 *			cuantas veces se repiten en este
	 * @param index Entero que indica en qué número de archivo vamos
	 * @return Cadedna que contiene todo el código html necesario para dibujar lo antes mencionado.
	 *		   Puede contener también estilos de css y además gráficos svg hechos con xml
	 */
	public String dibujaHTML(Diccionario<String,Integer> d, int index) {
		int c = 1;
		Rengloncillo[] renglones = ordena(d,index);
		ArbolRojinegro<Rengloncillo> rojillo = new ArbolRojinegro<>();
		/* Construimos los arboles */
		for (int i = renglones.length-1; i >= 0; i--) {
			rojillo.agrega(renglones[i]);
			if (i == renglones.length-15)
				break; // Sólo graficamos las 15 más usadas
		}
		Lista<String> temp = new Lista<>();
		ArbolAVL<Rengloncillo> avl = new ArbolAVL<>(rojillo);
		float[] porcentajes = calculaPorcentaje(renglones);
		float resto = -porcentajes[0];
		/* Empezamos a dibujar */
		String dibujo = INICIO_HTML;
		dibujo += String.format(ESTILO,"styles.css");
		dibujo += HEAD;
		dibujo += "\t<h1> Proyecto 3 EDD - Arroyo Lozano Santiago <br> Archivo: " + index + " </h1>\n";
		dibujo += "\t<h1>Gráfica de pastel</h1>\n";
		dibujo += "\t<svg viewBox=\"0 0 64 64\" class=\"pie\">\n";
		dibujo += String.format(PASTEL_INICIO,porcentajes[0]);
		temp.agrega(renglones[renglones.length-1].toString());
		for (int i = renglones.length-2; i >= 0; i--) {
			dibujo += String.format(PASTEL,porcentajes[c],colores[c],resto);
			resto -= porcentajes[c];
			temp.agrega(renglones[i].toString());
			c++;
			if (i == renglones.length-5)
				break; // Sólo graficamos las 5 más usadas
		}
		c = 0;
		dibujo += "\t</svg><br>\n";
		for (String str : temp) {
			dibujo += "\tPalabra: <p style=\"color:" + colores[c] + ";\">" + str + " - " + porcentajes[c] + "%</p>\n";
			c++;
		}
		dibujo += "\t<p style=\"color: crimson;\"> Resto de palabras - " + (100+resto) + "%</p>\n";
		dibujo += "\t<h1>Gráfica de Barras</h1>\n";
		dibujo += dibujaBarras(renglones);
		clase = "ArbolRojinegro";
		dibujo += "\t<h1>Arbol Rojinegro</h1>\n";
		dibujo += dibujaArbolBinario(rojillo);
		clase = "ArbolAVL";
		dibujo += "\t<h1>Arbol AVL</h1>\n";
		dibujo += dibujaArbolBinario(avl);
		return dibujo + FINAL_HTML;
	}

	/**
	 * Método auxiliar que ordena un diccionario a un arreglo de renglones
	 * El algoritmo de ordenamiento que usaremos será QuickSort
	 * Construimos renglones para no perder las veces que la palabra se repite en el archivo
	 * Además este algoritmo cuenta cada palabra, para saber así cuál es el total de palabras en el archivo
	 * @param d El diccionario a ordenar
	 * @param index El entero que indica en qué número de archivo vamos
	 * @return Un arreglo de renglones ordenado de menor a mayor
	 */
	private Rengloncillo[] ordena(Diccionario<String,Integer> d, int index) {
		Iterator<String> iteradorLlaves = d.iteradorLlaves();
		Rengloncillo[] renglones = new Rengloncillo[d.getElementos()];
		int i = 0;
		while (iteradorLlaves.hasNext()) {
			String k = iteradorLlaves.next();
			int v = d.get(k);
			renglones[i] = new Rengloncillo(k,v);
			if (k.length() >= 7)
				comunes.agrega(new Rengloncillo(k,index));
			cont += v; // Contamos
			i++;
		}
		/* Ordenamos */
		Arreglos.quickSort(renglones);
		return renglones;
	}

	/**
	 * Método auxiliar que genera un arreglo de floats ue indican el procentaje de cada palabra (cuanto se repite)
	 * El método acomoda el arreglo de tal manera que el primer elemento es el de mayor porcentaje
	 * @param renglones el arreglo de renglones que contiene las palabras más usadas y cuántas veces se repiten
	 * @return El arreglo float con los porcentajes de las 5 palabras más usadas
	 */
	private float[] calculaPorcentaje(Rengloncillo[] renglones) {
		float[] porcentajes = new float[5];
		int c = 0;
		for (int i = renglones.length-1; i >= 0; i--) {
			porcentajes[c] = (renglones[i].valor()*100)/cont;
			if (i == renglones.length-5)
				break; // Sólo calculamos las 5 más usadas
			c++;
		}
		System.out.println();
		return porcentajes;
	}

	/**
	 * Método auxiliar que dibuja una gráfica de barras en xml
	 * @param renglones Un arreglo ordenado de renglones, el cual
	 *					contiene las palabras y el valor entero de cuántas veces
	 *					se repiten en el archivo.
	 * @return Cadena que contiene todo el código necesario en xml para crear un svg
	 *		   de una gráfica de barras
	 */
	public String dibujaBarras(Rengloncillo[] renglones) {
		String dibujo = INICIO_BARRA;
		dibujo += TITULO;
		int k = 0;
		for (int i = renglones.length-1; i >= 0; i--) {
			int x = renglones[i].valor()*25+100;
			int y = k*40;
			dibujo += ABRE_G;
			dibujo += String.format(BARRA,x,y);
			dibujo += String.format(TEXTO_BARRA,x+5,y+20,renglones[i].toString() + " - " + renglones[i].valor() + " repeticiones");
			dibujo += CIERRA_G;
			if (i == renglones.length-5)
				break; // Sólo graficamos las 5 más usadas
			k++;
		}
		return dibujo;
	}

	/**
	 * Método que crea un archivo html y ademas indexa otros archivos html a él.
	 * Además dibujaremos el número total de palabras de cada archivo en una lista y
	 * dibujaremos también una gráfica, donde los vértices son los archivos y cada arista es una
	 * palabra de 7 o más letras que tengan en común
	 * @param totales Un arreglo de enteros, cada uno indicando el total de palabras en
	 *				   el archivo correspondiente a su índice más uno
	 * @param totalDic Una lista que contiene los diccionarios qu graficaron los archivos html
	 *					a indexar, esto para generar la gráfica, si es que tienen elementos en común
	 * @return Una cadena que contiene todo el código html necesario para dibujar el archivo, una lista
	 *			con los otros archivos indexados, el total de cada uno y una gráfica
	 */
	public String dibujaIndex(int[] totales, Lista<Diccionario<String,Integer>> totalDic) {
		String dibujo = INICIO_INDEX;
		Lista<Integer> graf = new Lista<>();
		/* Creamos la lista en html y una Lista que nos ayudará a graficar
		por omisión la lista ya contiene los vértices solos */
		for (int i = 0; i < totales.length; i++) {
			graf.agrega(i+1);
			graf.agrega(i+1);
			String path = "archivo"+(i+1)+".html";
			dibujo += String.format(INDEX,path,i+1);
			dibujo += "\t\tNúmero total de palabras: " + totales[i] + "\n";
		}
		dibujo += "\t</ol>\n";
		int i = 1;
		/* Si tienen una palabra en común creamos el arista */
		for (Diccionario<String,Integer> d : totalDic) {
			for (Rengloncillo r : comunes) {
				if (d.contiene(r.toString()) && i != r.valor()) {
					graf.agrega(i);
					graf.agrega(r.valor());
				}
			}
			i++;
		}
		dibujo += dibujaGrafica(graf);
		return dibujo + FINAL_HTML;
	}

	/**
	 * Método auxiliar que regresa la suma de todas las palabras procesadas por la clase
	 * @return Un número entero que contiene la suma de todas las palabras de un archivo
	 */
	public int suma() {
		int temp = cont;
		cont = 0;
		return temp;
	}

}//Cierre de la clase Grafica
