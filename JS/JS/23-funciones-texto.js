'use strict';

//Transformación de textos
var numero = 444;
var texto1 = "Bienvenido al curso de JavaScript de Victor Robles";
var texto2 = "es un buen curso";

var dato1 = numero.toString();
var dato2 = texto1.toLowerCase();
var dato3 = texto1.toUpperCase();

console.log("Número a String: " + dato1);
console.log("Mayúsculas a minúsculas: " + dato2);
console.log("Minúsculas a mayúsculas: " + dato3);

//Calcular la longitud
var nombre = "Santiago Arroyo";
console.log("El largo de mi nombre: ", nombre.length);	//... + nombre.length Lo hace string

var conArray = ["valor1", "valor2"];
console.log("Los valores en un arreglo: ", conArray.length);

//Concatenar - unir textos

var textoTotal = texto1.concat(" "+texto2);
/* Es lo mismo que:
var textoTotal = texto1 + " " + texto2;
*/
console.log(textoTotal);

//METODOS DE BUSQUEDA

var busqueda1 = texto1.indexOf("curso"); /*Es lo mismo escribir:
var busqueda1 = texto1.search("curso");*/
console.log(busqueda1);

var busqueda2 = textoTotal.match(/curso/gi);
console.log(busqueda2); //Lo regresa en un array, sirve para mutiples opciones

var busqueda = texto1.charAt(14,5); //Dame las primeras 5 letras que van después del caracter 14
console.log(busqueda);

busqueda = texto1.charAt(44);
console.log(busqueda);

busqueda = texto1.startsWith("Bi");
console.log(busqueda);

busqueda = texto1.includes("JavaScript");
console.log(busqueda);

//FUNCIONES REEMPLAZO
busqueda = texto1.replace("JavaScript", "Python");
console.log(busqueda);

busqueda = texto1.slice(14, 22);
console.log(busqueda);

busqueda = texto1.split(" "); //Divide el elemento en cada palabra y las pone en un array
console.log(busqueda);

busqueda = texto1.trim();
console.log(busqueda);
