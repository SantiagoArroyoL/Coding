package mx.unam.ciencias.edd.proyecto3;

/**
 * Proyecto 3: Contador de textos
 *
 * Enum que contiene el código XML necesario para dibujar ciertas figuras tales como circulos y rectángulos
 * además de contener la metadata necesaria para crear un archivo XML.
 * El enum cuenta con un constructor, ya que cada enum recibe una cadena.
 * Muchas de estas cadenas tienen valores por definir, esto hace que
 * podamos manipular el SVG para generar los graficos como nosotros necesitemos
 *
 * @author Arroyo Lozano Santiago
 * @version 2.0
 * @since 23/05/2020 - 12/06/2020
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

	/* Creamos un circulo de color y valores por definir con radio*/
	CIRCULO("\t\t<circle cx='%d' cy='%d' r='20' stroke='black' fill='%s' />\n"),

	/* Creamos un circulo de color y valores por definir */
	CIRCULO_R("\t\t<circle cx='%d' cy='%d' r='%d' stroke='black' fill='%s' />\n"),

	/* Creamos una línea negra que unirá los vertices de nuestras estructruas */
	LINEA("\t\t<line x1='%d' y1='%d' x2='%d' y2='%d' stroke='black'/>\n"),

	/* Cerramos el archivo html */
	FINAL_HTML("</body>\n</html>"),

	/* Damos inicio al archivo html e importamos lo necesario que se vea bonito */
	INICIO_HTML("<!DOCTYPE html>\n"
			+ "<html lang=\"es\" dir=\"ltr\">\n"
			+ "<html>\n"
			+ "<head>\n"
				+ "\t<meta charset=\"utf-8\">\n"
				+ "\t<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
				+ "\t<link rel=\"stylesheet\" href=\"https://stackpath.bootstrapcdn.com/bootstrap/4.4.1/css/bootstrap.min.css\" integrity=\"sha384-Vkoo8x4CGsO3+Hhxv8T/Q5PaXtkKtu6ug5TOeNV6gBiFeWPGFN9MuhOf23Q9Ifjh\" crossorigin=\"anonymous\">\n"
	),

	/* Etiqueta del estilo de css, que recibe la ruta necesaria al stykesheet */
	ESTILO("\t<link rel=\"stylesheet\" href=\"%s\">\n"),

	/* Etiqueta Head con mi nombre; EL punto es cerrarla */
	HEAD(		"\t<title>Arroyo Lozano Santiago - Proyecto3 EDD</title>\n"
			+ "</head>\n"
			+ "<body>\n"
	),

	/* Marca el inicio del archivo  html donde indexaremos todo */
	INICIO_INDEX("<!DOCTYPE html>\n"
			+ "<html lang=\"es\" dir=\"ltr\">\n"
			+ "<html>\n"
			+ "<head>\n"
				+ "\t<meta charset=\"utf-8\">\n"
				+ "\t<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
				+ "\t<link rel=\"stylesheet\" href=\"https://stackpath.bootstrapcdn.com/bootstrap/4.4.1/css/bootstrap.min.css\" integrity=\"sha384-Vkoo8x4CGsO3+Hhxv8T/Q5PaXtkKtu6ug5TOeNV6gBiFeWPGFN9MuhOf23Q9Ifjh\" crossorigin=\"anonymous\">\n"
			    + "\t<title>Arroyo Lozano Santiago - Proyecto3 EDD</title>\n"
			+ "</head>\n"
			+ "<body>\n"
			+ "\t<h1>Proyecto3 EDD! - Santiago Arroyo Lozano</h1>\n"
			+ "\t<ol>\n"
	),

	/* Etiqueta de un list item, para indexar algo */
	INDEX("\t\t<li><a href=\"%s\">Archivo %d</a></li>\n"),

	/* Iniciamos el svg de la grafica de barras */
	INICIO_BARRA("\t<svg class=\"chart\" width=\"1500\" height=\"200\" aria-labelledby=\"title desc\" role=\"img\">\n"),

	/* Titulo de la grafica de Barras */
	TITULO("\t\t<title id=\"title\">Grafica de barras</title>\n"),

	/* Abrimos una etiqueta para una barra indiviual */
	ABRE_G("\t\t<g class=\"bar\">\n"),

	/* Cerramos la barra individual */
	CIERRA_G("\t\t</g>\n"),

	/* Cerramos svg */
	CIERRA_SVG("\t</svg>\n"),

	/* La barra indiviual */
	BARRA("\t\t\t<rect width=\"%d\" height=\"39\" y=\"%d\"></rect>\n"),

	/* La etiqueta que genera la grafca de pastel */
	PASTEL_INICIO("\t\t<circle r=\"25%%\" cx=\"50%%\" cy=\"50%%\" style=\"stroke-dasharray: %2f 100\"></circle>\n"),

	/* Cada gajo de la gráfica de pastel */
	PASTEL("\t\t<circle r=\"25%%\" cx=\"50%%\" cy=\"50%%\" style=\"stroke-dasharray: %2f 100; stroke: %s; stroke-dashoffset: %2f;\"></circle>\n"),

	/* El texto que indica los valores de la barra */
	TEXTO_BARRA("\t\t\t<text x=\"%d\" y=\"%d\" dy=\".35em\">%s</text>\n");

	/* La linea de cada ENUM */
	private String linea;

	/**
	 * Constructor de nuestros ENUM
	 * @param linea EL valor en cadena que tendrá cada valor de nuestro ENUM
	 */
    private Svg(String linea) {
        this.linea = linea;
    }

	/** Método que nos regresa el valor String contenido en cada ENUM
	 * @return el valor en cadena de cada enum
	 */
    public String getLinea() {
        return this.linea;
    }
}//Cierre del enum SVG
