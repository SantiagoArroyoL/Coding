'use strict'

//Parametros REST y SPREAD

function listadoFrutas(fruta1, fruta2, ...resto_de_frutas){
	console.log("Fruta 1: ",fruta1);
	console.log("Fruta 2: ",fruta2);
	console.log("Resto de frutas: ",resto_de_frutas);
}

listadoFrutas("Naranja", "Manzana", "Toronja", "Uva", "Guanabana");
console.log("*****************************");

var frutas = ["Naranja", "Manzana"];
listadoFrutas(...frutas, "Toronja", "Uva", "Guanabana");

//Poner los tres putos es otra forma de declarar un arreglo. "resto_de_frutas" es un parámetro REST (Porque todas las frutas van a estar en un mismo valor) y "frutas" es un parámetro SPREAD, porque es un sólo array pero por los tres puntos se desglosa y te los ponen uno por uno
