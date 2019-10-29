'use strict';
//ARRAYS MULIDIMENSIONALES

var categorías = ['Acción', 'Terror', 'Comedia'];
var peliculas = ['La verdad duele', 'la vida es bella', 'Avengers']

var cine = [categorías, peliculas];
// console.log(cine[0][1]);
// console.log(cine[1][2]);

// OPERACIONES CON LOS ARRAY

var elemento = "";

do{
	elemento = prompt("Introduce tu pelicula:");
	peliculas.push(elemento);
}while(elemento != "ACABAR")

// peliculas.pop();//Elimina el elemento de un array
// console.log(peliculas);

//otra manera de borrar
// var indice = peliculas.indexOf('Avengers');
//
// if (indice > -1) {
// 	peliculas.splice(indice, 1);
// }

//hacer un array texto
var peliculas_string = peliculas.join();

console.log(peliculas);
	console.log(peliculas_string);

//converitr String en un array
var cadena = "texto1, texto2, texto3";
var cadena_array = cadena.split(", ");

console.log(cadena);
console.log(cadena_array);

//ORDENAR UN ARRAYS
peliculas.sort(); //Lo hace en orden alfabético
console.log(peliculas);
peliculas.reverse();
console.log(peliculas);
