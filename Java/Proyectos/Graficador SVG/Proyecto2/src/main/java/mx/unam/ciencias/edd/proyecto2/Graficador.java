package mx.unam.ciencias.edd.proyecto2;

import mx.unam.ciencias.edd.*;

public class Graficador {

	/* Cadena que define con qué clase estamos trabajando */
	private String clase;
	private VerticeArbolBinario<Integer> v;

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
	/* Etiqueta para círculo de gráfica y árboles */
	private final String CIRCULO = Svg.CIRCULO.getLinea();
	/* Linea rvitraria para Pilas */
	private final String POLYLINE = Svg.POLYLINE.getLinea();
	/* Etiqueta para rectángulos. */
	private final String RECTANGULO = Svg.RECTANGULO.getLinea();
    /* Etiqueta para texto en ǵráficas. */
    private final String TEXTOCHICO = Svg.TEXTOCHICO.getLinea();
	/* Etiqueta para línea de gráfica. */
	private final String LINEAGRANDE = Svg.LINEAGRANDE.getLinea();

	/**
	 * Constructor de nuestra clase Grafica
	 * @param clase String que define con qué clase estamos trabajando
	 */
	public Graficador(String clase) {
		this.clase = clase;
	}

	/**
	 * @throws IllegalArgumentException si el elemento es <code>null</code> o ya
	 */
	public String graficaColeccion(Coleccion<Integer> listaFinal) {
		switch (clase) {
			case "Lista": {
					return dibujaLista((Lista<Integer>)listaFinal);
			} case "ArbolAVL": {
				ArbolAVL<Integer> arbolAvl = new ArbolAVL<>(listaFinal);
				return dibujaArbolBinario(arbolAvl);
			} case "ArbolBinarioCompleto": {
				ArbolBinarioCompleto<Integer> arbolCompleto = new ArbolBinarioCompleto<>(listaFinal);
				return dibujaArbolBinario(arbolCompleto);
			} case "ArbolBinarioOrdenado": {
				ArbolBinarioOrdenado<Integer> arbolOrdenado = new ArbolBinarioOrdenado<>(listaFinal);
				return dibujaArbolBinario(arbolOrdenado);
			} case "ArbolRojinegro": {
				ArbolRojinegro<Integer> arbolRojito = new ArbolRojinegro<>(listaFinal);
				return dibujaArbolBinario(arbolRojito);
			} case "Cola": {
				Cola<Integer> colaFinal = new Cola<>();
				for (int i : listaFinal)
					colaFinal.mete(i);
				return dibujaMeteSaca(colaFinal);
			} case "Pila": {
				Pila<Integer> pilaFinal = new Pila<>();
				for (int i : listaFinal)
					pilaFinal.mete(i);
				return dibujaMeteSaca(pilaFinal);
			} default: {
				System.out.println("La clase introducida no es válida");
				System.exit(-1);
			}
		}//Cierre del switch
		return "";
	}

	private String dibujaLista(Lista<Integer> listaFinal) {
		String dibujo = INICIO;
		int tamaño, i;
		tamaño = 50*listaFinal.getLongitud() + 10*listaFinal.getLongitud()-1;
		i = 1;
		/* Para cada elemento en el dibujo debemos crear el rectángulo
		El indice i nos ayudará para saber en qué rectangulo vamos */
		for (int elemento : listaFinal) {
			dibujo += String.format(RECTANGULO,60*i,10,50,20);
			if (i+1 < listaFinal.getLongitud()+1)
				dibujo += String.format(FLECHA,10,60*(i+1)-5,20, "&#x2194;");
			dibujo += String.format(TEXTO,60*i+25,26,"black",elemento);
			i++;
		}
		dibujo += CIERRA;
		return dibujo;
	}


	public String dibujaMeteSaca(MeteSaca<Integer> instancia) {
		String dibujo = INICIO;
		Lista<String> lineas = new Lista<String>();
		int i = 0;
		if (clase.equals("Pila")) {
			int alturaTotal;
			while (!instancia.esVacia()) {
				int elemento = instancia.saca();
				lineas.agrega(String.format(TEXTO,27,(30*i)+35,"black",elemento));
				i++;
			}
			alturaTotal = 20*(i+1) + 10*i;
			dibujo += String.format(POLYLINE,alturaTotal,alturaTotal);
			for (String s : lineas)
				dibujo += s;
			dibujo += CIERRA;
			return dibujo;
		}
		i = 1;
		int anchuraTotal;
		while (!instancia.esVacia()) {
			int elemento = instancia.saca();
			lineas.agrega(String.format(TEXTO,(60*i)+25,25,"black",elemento));
			i++;
		}
		anchuraTotal = 50*i + 10*(i-1);
		dibujo += String.format(FLECHA,30,55,25,"&#x2190;");
		dibujo += String.format(LINEA,60,5,anchuraTotal,5);
		for (String s : lineas)
			dibujo += s;
		dibujo += String.format(LINEA,60,30,anchuraTotal,30);
		dibujo += String.format(FLECHA,30,60*i-5,25,"&#x2190;");
		dibujo += CIERRA;
		return dibujo;
	}


	/**
	* Dibuja un árbol binario de cualquier tipo.
	* @return el código SVG del árbol binario.
	*/
	public String dibujaArbolBinario(ArbolBinario<Integer> arbol) {
		System.out.println(arbol);
		Cola<VerticeArbolBinario<Integer>> colita = new Cola<>();
		String dibujo = INICIO;
		Lista<String> circulos = new Lista<String>();
		v = arbol.raiz();
		colita.mete(v);
		int x = 0,y = 0;
		while (!colita.esVacia()) {
			VerticeArbolBinario<Integer> temp = colita.saca();
			if (cambiaAltura(temp)) {
				v = temp;
				x = 80*temp.altura()+60;
			} else {
				x += 160;
			}
			y = 100*temp.profundidad()+30;
			if (temp.hayIzquierdo())
				colita.mete(temp.izquierdo());
			if (temp.hayDerecho())
				colita.mete(temp.derecho());
			if (temp.hayPadre())
				if (esDerecho(temp))
					dibujo += String.format(LINEA,x,y,x-80,y-100);
				else
					dibujo += String.format(LINEA,x,y,x+80,y-100);
			if (clase.equals("ArbolRojinegro"))
				circulos.agrega(dibujaVerticeRojinegro(temp,x,y));
			else
				circulos.agrega(dibujaVertice(temp,x,y));
		}
		for (String str : circulos) {
			dibujo += str;
		}
		dibujo += CIERRA;
		return dibujo;
	}

	private boolean cambiaAltura(VerticeArbolBinario<Integer> temp) {
		if (!v.hayPadre())
			return true;
		return temp.padre() != v.padre();
	}

	private String dibujaVertice(VerticeArbolBinario<Integer> v, int x, int y) {
		String dibujoAux = "";
		String balance;
		dibujoAux += String.format(CIRCULO,x,y,"white");
		dibujoAux += String.format(TEXTO,x,y+5,"black",v.get());
		if (clase.equals("ArbolAVL")){
			String[] temp = v.toString().split(" ");
			balance = "[" + temp[1] + "]";
			dibujoAux += String.format(TEXTO,x-35,y-15,"black",balance);
		}
		return dibujoAux;
	}

	private String dibujaVerticeRojinegro(VerticeArbolBinario<Integer> v, int x, int y) {
		String color;
		ArbolRojinegro<Integer> a = new ArbolRojinegro<>();
		a.agrega(0);
		if  (a.getColor(v) == Color.ROJO)
			color = "red";
		else
			color = "black";
		String dibujoAux = "";
		dibujoAux += String.format(CIRCULO,x,y,color);
		dibujoAux += String.format(TEXTO,x,y+5,"white",v.get());
		return dibujoAux;
	}

	private String dibujaGrafica(Grafica g) {
		return "";
	}

	/**
	 * Método que nos indica si el hijo es derecho
	 * @param v El vertice a comparar
	 * @return true en caso de serlo, false en caso contrario
	 */
	private boolean esDerecho(VerticeArbolBinario<Integer> v) {
		//Comparamos con == puesto que deben ser la misma referencia
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

}
