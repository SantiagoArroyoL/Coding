'use strict'

/*
1. Pida 6 números por pantalla y los meta en un array
2. Mostrar el array entero (todos sus elementos) en el cuerpo de la página y en la consola
3. Ordenar el array y mostrarlo
4. Invertir su orden y mostrarlo
5. Mostrar cuántos elementos tiene el array
6. Hacer una busquea de un valor introducido por el usuario, además que nos diga si lo encuentra y su indice
(Se valorará el uso de funciones)
*/
function mostrarArray (elementos, customText = ""){
	document.write("<h1>Contenido del Array "+customText+":</h1>");
	document.write("<ul>");
	elementos.forEach((elemento, index) => {
		document.write("<li>"+elemento+"</li>");
	})
	document.write("</ul>");
}
//1
// var numeros = new Array(6);
var numeros = [];

for (var i = 0; i <= 5; i++) {
	//numeros[i] = parseInt(prompt("Introduce un número", 0));
	numeros.push(parseInt(prompt("Introduce un número")));
}

//2
mostrarArray(numeros);
console.log(numeros);

//3
numeros.sort();
mostrarArray(numeros, "Ordenado");

//4
numeros.reverse();
mostrarArray(numeros, 'Invertido');

//5
document.write("<h1>El Array tiene: "+numeros.length+" elementos");

//6
var busqueda = parseInt(prompt("Busca un número"));

var posicion = numeros.findIndex(numero => numero == busqueda);

if (posicion && posicion != -1) {
	document.write("<hr><h1>ENCONTRADO</h1><hr>");
	document.write("<h1>Posición de la busqueda: "+posicion+"</h1>");
}else {
	alert('No encontrado');
}
