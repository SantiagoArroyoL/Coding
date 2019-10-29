'use strict'

//Condicional IF
var n = 30;
var m = 40;

if (n < m) {
	console.log("N es menor que M");
}
/*
Operadores relacionales:
	Mayor qué: >
	Menor qué: <
	Mayor o igual: >=
	Menor o igual: <=
	Igual: ==
	Distinto: !=
Operadores lógicos:
	AND(Y): &&
	OR(O): ||
	Negación(NO): !
*/
var edad = 17;
var nombre = "Santiago";
var year = 2001;

if (edad >= 18 || edad <=17) {
	console.log(nombre + "tiene " + edad + "años, es mayor de edad");

	if (edad >= 33) {
		console.log("Eres un millenial");
	}
	else if(edad >= 73){
		console.log("Eres de la tercera edad");
	}
	else {
		console.log("No eres un millenial");
	}
}
else {
	console.log(nombre + " tiene " + edad + "  años, no es mayor de edad");
}

if (year !>= 2000) {
	console.log(nombre + " nació en este milenio");
}
else {
	console.log(nombre + " no nació en este milenio");
}
