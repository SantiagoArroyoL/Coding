package mx.unam.ciencias.edd.proyecto2;

/**
 * Proyecto 2: Graficador SVG

 * Enum que contiene el código XML necesario para dibujar ciertas figuras tales como circulos y rectángulos
 * además de contener la metadata necesaria para crear un archivo XML.
 * El enum cuenta con un constructor, ya que cada enum recibe una cadena.
 * Muchas de estas cadenas tienen valores por definir, esto hace que
 * podamos manipular el SVG para generar los graficos como nosotros necesitemos
 *
 * @author Arroyo Lozano Santiago
 * @version 1.0
 * @since 11/04/2020 - 28/04/2020.
 */
public enum Svg {

    /** Inicia el XML versión 1 con encoding UTF_8 y además inicia la gráfica.
	*    Notemos que los valores de 'width' y 'height' están por definirse */
	INICIO("<?xml version=\'1.0\' encoding=\'UTF-8\' ?> \n<svg xmlns= \'http://www.w3.org/2000/svg\' xmlns:xlink ='http://www.w3.org/199/xlink' width='%d' height='%d'>\n<!--\nGraficador hecho por Santiago Arroyo Lozano \nClase graficada: %s \n-->\n\t<g>\n"),

	/* Cerramos tanto la gráfica como el archivo XML */
	CIERRA("\t</g>\n</svg>\n"),

	/* POLYLINE es una linea que cuenta con n puntos, la usaremos sólo para pilas */
	POLYLINE("\t\t<polyline points=\"10,10 10,%d %d,%d %d,10\" style=\"fill:white;stroke:black;stroke-width:4\" />\n"),

	/* Con este comando hacemos una rectangulo negro con interior blanco con valores por definirse*/
	RECTANGULO("\t\t<rect x='%d' y='%d' width='%d' height='%d' stroke='black' fill='white'/>\n"),

	/* Creamos texto con fuente sans-serif y tamaño 14 en donde los valores por definirse indiquen */
	TEXTO("\t\t<text font-family='sans-serif' font-size='18' x='%d' y='%d' text-anchor='middle' fill='%s'>%s</text>\n"),

	/* Dibujamos un gráfico por definir negro que conectará nuestras estructuras lineales */
	FLECHA("\t\t<text fill='black' font-family='sans-serif' font-size='%d' x='%d' y='%d' text-anchor='middle'>%s</text>\n"),

	/* Creamos un circulo de color y valores por definir */
	CIRCULO("\t\t<circle cx='%d' cy='%d' r='20' stroke='black' fill='%s' />\n"),

	/* Creamos una línea negra que unirá los vertices de nuestras estructruas */
	LINEA("\t\t<line x1='%d' y1='%d' x2='%d' y2='%d' stroke='black'/>\n");

	/* La linea de cada ENUM */
	private String linea;

	/**
	 * Constructor de nuestros ENUM
	 * @param linea EL valor en cadena que tendrá cada valor de nuestro ENUM
	 */
    Svg(String linea) {
        this.linea = linea;
    }

	/** Método que nos regresa el valor String contenido en cada ENUM
	 * @return el valor en cadena de cada enum
	 */
    public String getLinea() {
        return this.linea;
    }
}//Cierre del enum SVG
