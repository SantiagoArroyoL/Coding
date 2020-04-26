package mx.unam.ciencias.edd.proyecto2;

import mx.unam.ciencias.edd.*;
import java.lang.Math;

public class Graficador {

	/* Cadena que define con qué clase estamos trabajando */
	private String clase;

	/* Etiqueta para texto. */
	private final String TEXTO = Svg.TEXTO.getLinea();
	/* Etiqueta para línea. */
	private final String LINEA = Svg.LINEA.getLinea();
	/* Etiqueta para línea con valores double */
	private final String LINEA_G = Svg.LINEA_G.getLinea();
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
			case "Grafica": {
				if (listaFinal.getElementos() % 2 != 0) {
					System.err.println("Por favor introduce un número par de elementos");
					System.exit(-1);
				}
				int temp = 0, i = 1;
				Grafica<Integer> g = new Grafica<>();
				for (int elemento : listaFinal) {
					try {
						g.agrega(elemento);
					} catch (IllegalArgumentException iae) {
						/* No hacemos nada. Aumentaría la commplejidad si antes de agregar nos
						 * seguramos que no contenga al vértice 2 veces porque habría que recorrer
						 * la lista de vértices. Este error se dispara en los casos cuando el vértice
						 * está sólo o cuando se agrega un nuevo arista al mismo vértice */
					}
					if (i % 2 == 0 && temp != elemento)
						g.conecta(temp, elemento);
					i++;
					temp = elemento;
				}
				return dibujaGrafica(g);
			}case "MonticuloMinimo": {
				int v = 0;
				MonticuloMinimo<ValorIndexable<Integer>> monty = new MonticuloMinimo<>();
				for (int i : listaFinal) {
					monty.agrega(new ValorIndexable<Integer>(i,v));
					v++;
				}
				return dibujaMonticulo(monty);
			} default: {
				System.err.println("La clase introducida no es válida");
				System.exit(-1);
			}
		}//Cierre del switch
		return "";
	}

	private String dibujaArreglo(Lista<Integer> listaFinal) {
		int tamaño, i;
		tamaño = 50*listaFinal.getLongitud() + 10*listaFinal.getLongitud()-1;
		String dibujo = String.format(INICIO,tamaño+200,200);
		/* Para cada elemento en el dibujo debemos crear el rectángulo
		El indice i nos ayudará para saber en qué rectangulo vamos */
		i = 1;
		for (int elemento : listaFinal) {
			dibujo += String.format(RECTANGULO,60*i,10,60,20);
			dibujo += String.format(TEXTO,60*i+30,26,"black",elemento);
			i++;
		}
		dibujo += CIERRA;
		return dibujo;
	}

	private String dibujaLista(Lista<Integer> listaFinal) {
		int tamaño, i;
		tamaño = 50*listaFinal.getLongitud() + 10*listaFinal.getLongitud()-1;
		String dibujo = String.format(INICIO,tamaño+200,200);
		/* Para cada elemento en el dibujo debemos crear el rectángulo
		El indice i nos ayudará para saber en qué rectangulo vamos */
		i = 1;
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


	public String dibujaMeteSaca(Lista<Integer> listaFinal) {
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
				if(String.valueOf(elemento).length() > anchuraTotal)
					anchuraTotal = String.valueOf(elemento).length();
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
			String dibujo = String.format(INICIO,anchuraTotal*50,alturaTotal+30);
			dibujo += String.format(POLYLINE,alturaTotal,anchura,alturaTotal,anchura);
			for (String s : lineas)
				dibujo += s;
			dibujo += CIERRA;
			return dibujo;
		}
		i = 1;
		while (!pilaFinal.esVacia()) {
			int elemento = pilaFinal.saca();
			lineas.agrega(String.format(TEXTO,(60*i)+25,25,"black",elemento));
			i++;
		}
		anchuraTotal = 50*i + 10*(i-1);
		String dibujo = String.format(INICIO,anchuraTotal+50,alturaTotal);
		dibujo += String.format(FLECHA,30,55,25,"&#x2192;");
		dibujo += String.format(LINEA,60,5,anchuraTotal,5);
		for (String s : lineas)
			dibujo += s;
		dibujo += String.format(LINEA,60,30,anchuraTotal,30);
		dibujo += String.format(FLECHA,30,60*i-5,25,"&#x2192;");
		dibujo += CIERRA;
		return dibujo;
	}


	/**
	* Dibuja un árbol binario de cualquier tipo.
	* @param arbol El arbol a graficar
	* @return el código SVG del árbol binario.
	*/
	public String dibujaArbolBinario(ArbolBinario<Integer> arbol) {
		int y, a = arbol.altura();
		String dibujo = String.format(INICIO,a*1000,a*125);
		Lista<String> circulos = new Lista<String>();
		VerticeArbolBinario<Integer> v = arbol.raiz();
		Lista<VerticeArbolBinario<Integer>> vertices = new Lista<>();
		int[] padres = new int[arbol.getElementos()];
		Cola<VerticeArbolBinario<Integer>> colita = new Cola<>();
		int tempY = 100*v.profundidad()+30;
		int x = 150*v.altura()+80;
		if (clase.equals("ArbolBinarioOrdenado") && v.altura() > 6)
		    x = 50*v.altura()+80;
		int separacion = x+700;
		colita.mete(v);
		while (!colita.esVacia()) {
			VerticeArbolBinario<Integer> temp = colita.saca();
			y = 100*temp.profundidad()+30;
			if (y != tempY)	{
				separacion = separacion/2;
				tempY = y;
			}
			if (temp.hayPadre()) {
				int i = vertices.indiceDe(temp.padre());
				if(esDerecho(temp))
					x = padres[i]+separacion/2;
				else
					x = padres[i]-separacion/2;
			}
			if (temp.hayIzquierdo()) {
				colita.mete(temp.izquierdo());
				dibujo += String.format(LINEA,x,y,x-(separacion/2)/2,y+100);
			}
			if (temp.hayDerecho()) {
				colita.mete(temp.derecho());
				dibujo += String.format(LINEA,x,y,x+(separacion/2)/2,y+100);
			}
			if (temp.hayDerecho() || temp.hayIzquierdo()){
				vertices.agrega(temp);
				padres[vertices.indiceDe(temp)] = x;
			}
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

	private String dibujaVertice(VerticeArbolBinario<Integer> v, int x, int y) {
		String balance;
		String dibujoAux = String.format(CIRCULO,x,y,"white");
		dibujoAux += String.format(TEXTO,x,y+5,"black",v.get());
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

	private String dibujaVertice(VerticeGrafica<Integer> v, int x, int y) {
		String dibujoAux = String.format(CIRCULO,x,y,"white");
		dibujoAux += String.format(TEXTO,x,y+5,"black",v.get());
		return dibujoAux;
	}

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

	private String dibujaGrafica(Grafica<Integer> g) {
		final double angulo = 360 / g.getElementos();
    	final int radio = 40 * g.getElementos();
    	final int centro = radio + 25;
		final Lista<Integer> lista = new Lista<>();
		final Lista<String> lineas = new Lista<>();
		final int tamaño = g.getElementos()*250;
		final double[] ang = {angulo};
		for (int i : g)
			lista.agrega(i);
		g.paraCadaVertice((v) -> {

			int x = calculaCoordenadaX(ang[0],radio);
			int y = calculaCoordenadaY(ang[0],radio);

			/* Verifica los vecinos de v. */
			for(VerticeGrafica<Integer> vecino : v.vecinos()){
				if(vecino.getColor() != Color.ROJO){
					int i = lista.indiceDe(vecino.get());
					int auxX = calculaCoordenadaX((i+1)*angulo,radio);
					int auxY = calculaCoordenadaY((i+1)*angulo,radio);
					/* Conecta las cordenadas del vertice v con las del vecino.*/
					lineas.agrega(String.format(LINEA,centro+x,centro-y,centro+auxX, centro-auxY));
				}
			}
			lineas.agrega(dibujaVertice(v,centro+x,centro-y));
			double auxAng = ang[0];
			auxAng += angulo;
			ang[0] = auxAng;
			g.setColor(v,Color.ROJO);
		});
		String dibujo = String.format(INICIO,tamaño,tamaño);
		for (String str : lineas) {
			dibujo += str;
		}
		dibujo += CIERRA;
		return dibujo;
	}

	/**
    * Método auxiliar que calcula las coordenadas de los vértices basándose en
    * el ángulo que reciba. Se necesita mover en el eje X usando coseno.
    * @return la coordenada X.
	*/
	private int calculaCoordenadaX(double angulo, int radio){
		return (int) Math.floor(Math.cos(Math.toRadians(angulo)) * radio) ;
	}

	/**
	* Método auxiliar que calcula las coordenadas de los vértices basándose en
	* el ángulo que reciba. Se necesita mover en el eje Y usando seno.
	* @return la coordenada Y.
	*/
	private int calculaCoordenadaY(double angulo, int radio){
		return (int) Math.floor(Math.sin(Math.toRadians(angulo)) * radio);
	}

	private String dibujaMonticulo(MonticuloMinimo<ValorIndexable<Integer>> monty) {
		return "";
	}
}
