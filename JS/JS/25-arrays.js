'use strict';

//Arrays, Arreglos, Matrices

var nombre = "Victor Robles";
var nombres = ["Victor Robles", "Santiago Arroyo", "Andrés Patiño", 52, true];

var lenguajes = new Array("PHP", "JS", "Go", "Java");

var elemento = parseInt(prompt("Qué elemento del array quieres?", 0));
if (elemento >= nombres.length) {
	alert("Introduce un número menor que: " + nombres.length);
} else {
	alert("El usuario seleccionado es: " + nombres[elemento]);
}

document.write("<h1>Lenguajes de programación del 2018 </h1>");
document.write("<ul>");

/*for (var i = 0; i < lenguajes.length; i++) {
	document.write("<li>"+lenguajes[i]+"</li>");
}*/ //ES MEJOR:
// lenguajes.forEach((elemento, index, arr)=>{
// 	document.write("<li>"+index+" - "+elemento+"</li>");
// });

//Otra manera de hacerlo es con el for in
for (let lenguaje in lenguajes) {
	document.write("<li>"+lenguajes[lenguaje]+"</li>");
}

document.write("</ul>");

//BUSQUEDA EN UN ARRAY
var precios = [10, 20, 20, 80];
var busqueda1 = precios.some(precios => precios > 80);

/*
var busqueda = lenguajes.find(function(lenguaje){
	return lenguaje == "PHP";
});
*/ //Esto se resume así:
var busqueda2 = lenguajes.find(lenguaje => lenguaje == "PHP");
console.log(busqueda1);
console.log(busqueda2);
