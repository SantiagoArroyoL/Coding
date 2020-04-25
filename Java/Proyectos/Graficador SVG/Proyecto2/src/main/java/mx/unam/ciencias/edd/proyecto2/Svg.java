package mx.unam.ciencias.edd.proyecto2;

/**
 * Enumeración de comandos XML. Para mantener el códgio más limpio añadimos cada línea de
 */
public enum Svg {

    /** Inicia el XML versión 1 con encoding UTF_8 y además inicia la gráfica.
	*    Notemos que los valores de 'width' y 'height' están por definirse */
	INICIO("<?xml version=\'1.0\' encoding=\'UTF-8\' ?> \n<svg xmlns= \'http://www.w3.org/2000/svg\' xmlns:xlink ='http://www.w3.org/199/xlink' width='2000' height='2000'>\n \t<g>\n"),

	/* Cerramos tanto la gráfica y el archivo XML */
	CIERRA("\t</g>\n</svg>\n"),

	POLYLINE("\t\t<polyline points=\"10,10 10,%d 45,%d 45,10\" style=\"fill:white;stroke:black;stroke-width:4\" />\n"),

	/* Con este comando hacemos una rectangulo negro con interior blanco con valores por definirse*/
	RECTANGULO("\t\t<rect x='%d' y='%d' width='%d' height='%d' stroke='black' fill='white'/>\n"),

	/* Creamos texto con fuente sans-serif y tamaño 14 en donde los valores por definirse indiquen */
	TEXTO("\t\t<text font-family='sans-serif' font-size='18' x='%d' y='%d' text-anchor='middle' fill='%s'>%s</text>\n"),

	/* Lo mismo que la línea anterior pero tamaño 12 */
	TEXTOCHICO("\t\t<text font-family='sans-serif' font-size='12' x='%f' y='%f' ext-anchor='middle' fill='%s'>%s</text>\n"),

	/* Dibujamos una fecha negra que conectará nuestras estructuras lineales */
	FLECHA("\t\t<text fill='black' font-family='sans-serif' font-size='%d' x='%d' y='%d' text-anchor='middle'>%s</text>\n"),

	/* Creamos un circulo de color y valores por definir */
	CIRCULO("\t\t<circle cx='%d' cy='%d' r='20' stroke='black' fill='%s' />\n"),

	/* Creamos una línea negra que unirá los circulos de los árboles */
	LINEA("\t\t<line x1='%d' y1='%d' x2='%d' y2='%d' stroke='black'/>\n"),

	/* Lo mismo que la línea anterior pero de mayor tamaño */
	LINEAGRANDE("\t\t<line x1='%f' y1='%f' x2='%f' y2='%f'"+ " stroke='black' stroke-width='1'/>\n");

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
}
