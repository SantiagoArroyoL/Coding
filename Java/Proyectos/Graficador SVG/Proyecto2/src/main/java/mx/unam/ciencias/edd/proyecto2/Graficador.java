package mx.unam.ciencias.edd.proyecto2;

import mx.unam.ciencias.edd.*;

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
	/* Etiqueta para conectar las estructuras lineales. */
	private final String CONECTOR_LISTA = Svg.CONECTOR_LISTA.getLinea();

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
				Cola<Integer> colita = new Cola<>();
				for (int i : listaFinal)
					colita.mete(i);
				return dibujaMeteSaca(colita);
			} case "Pila": {
				Pila<Integer> pilota = new Pila<>();
				for (int i : listaFinal)
					pilota.mete(i);
				return dibujaMeteSaca(pilota);
			} default: {
				System.out.println("La clase introducida no es válida");
				System.exit(-1);
			}
		}//Cierre del switch
		return "";
	}

	private String dibujaLista(Lista<Integer> listaFinal) {
		String dibujo = "";
		int tamaño, i;
		tamaño = 50*listaFinal.getLongitud() + 10*listaFinal.getLongitud()-1;
		/* Iniciamos el canvas con el tamaño de la lista */
		dibujo += String.format(INICIO,tamaño,20);
		i = 0;
		/* Para cada elemento en el dibujo debemos crear el rectángulo
		El indice i nos ayudará para saber en qué rectangulo vamos */
		for (int elemento : listaFinal) {
			dibujo += String.format(RECTANGULO,60*i,0,50,20);
			if (i+1 < listaFinal.getLongitud())
				dibujo += dibujaConector(CONECTOR_LISTA,10,60*(i+1)-5,13, "&#x2194;");
			dibujo += String.format(TEXTO,60*i+25,13,"black",elemento);
			i++;
		}
		dibujo += CIERRA;
		return dibujo;
	}


	public String dibujaMeteSaca(MeteSaca<Integer> instancia) {
		String dibujo = "";
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
			dibujo += String.format(INICIO,50,alturaTotal+50);
			dibujo += String.format(POLYLINE,alturaTotal,alturaTotal);
			for (String s : lineas)
				dibujo += s;
			dibujo += CIERRA;
			return dibujo;
		}
		int anchuraTotal;
		while (!instancia.esVacia()) {
			int elemento = instancia.saca();
			lineas.agrega(String.format(TEXTO,(60*i)+25,25,"black",elemento));
			i++;
		}
		anchuraTotal = 50*(i+1) + 10*i;
		dibujo += String.format(INICIO,anchuraTotal,35);
		dibujo += String.format(LINEA,0,5,anchuraTotal,5);
		for (String s : lineas)
			dibujo += s;
		dibujo += String.format(LINEA,0,30,anchuraTotal,30);
		dibujo += dibujaConector(CONECTOR_LISTA,10,60*(i+1)-5,25,"&#x2190;");
		dibujo += CIERRA;
		return dibujo;
	}


	/**
	* Dibuja un árbol binario de cualquier tipo.
	* @return el código SVG del árbol binario.
	*/
	public String dibujaArbolBinario(ArbolBinario<Integer> arbol) {
		System.out.println(arbol);
		System.out.println("*******************************************************");
		Cola<VerticeArbolBinario<Integer>> cola = new Cola<VerticeArbolBinario<Integer>>();
		String dibujo =  String.format(INICIO,arbol.altura()*500,arbol.altura()*100);
		VerticeArbolBinario<Integer> v = arbol.raiz();
		cola.mete(v);
		int x = 30, y = 30;
		while (!cola.esVacia()) {
			VerticeArbolBinario<Integer> temp = cola.saca();
			if (temp.hayIzquierdo())
				cola.mete(temp.izquierdo());
			if (temp.hayDerecho())
				cola.mete(temp.derecho());
			dibujo += dibujaVertice(temp,x,y);
			x += 50;
			y = v.altura()*30;
		}
		dibujo += CIERRA;
		return dibujo;
	}

	private String dibujaVertice(VerticeArbolBinario<Integer> v, int x, int y) {
		String dibujoAux = "";
 		if (clase.equals("ArbolRojinegro")) {
			dibujoAux += String.format(CIRCULO,x,y,"red","red");
			dibujoAux += String.format(TEXTO,x,y,"white",v.get());
		} else {
			dibujoAux += String.format(CIRCULO,x,y,"black","white");
			dibujoAux += String.format(TEXTO,x,y,"black",v.get());
		}

		return dibujoAux;
	}

	private String dibujaGrafica(Grafica g) {
		return "";
	}


	/**
	* Método auxiliar que dibuja un conector en las estructuras lineales.
	* @return el código SVG para un conector lineal.
	*/
	public String dibujaConector(String cons, int size, int x, int y, String conector) {
		return String.format(cons,size,x,y,conector);
	}

}
