'use strict'

// JSON - JavaScript Object Notation

var pelicula = {
	titulo: 'Batman vs Superman',
	year: 2016,
	pais: 'Estados Unidos'
};
/* Y así defines un objeto JSON en JavaScript.
 * Puta madre que facil es en comparación con Java
*/

pelicula.titulo = "Batman v Superman";
/* NO hay encapsulamiento de datos en JS */
var peliculas = [
	{titulo: "La verdad duele", year: 2016, pais: "Francia"}, pelicula
];

var index;
var cajaPeliculas = document.querySelector("#peliculas");
for (index in peliculas) {
	var p = document.createElement("p");
	p.append(peliculas[index].titulo + " - " + peliculas[index].year);
	cajaPeliculas.append(p);
}
