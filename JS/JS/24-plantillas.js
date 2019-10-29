'use strict';

//Plantillas de texto

var nombre = prompt("Dame tu nombre");
var apellidos = prompt("Dame tus apellidos");

//var texto = "mi nombre es: " + nombre + " <br> Mis apellidos son: " + apellidos;
var texto = `
	<h1> Hola que tal</h1>
	<h3>Mi nombre es: ${nombre}</h3>
	<h3>Mis apellidos son: ${apellidos}</h3>
`; //Comilla invertida (acento invertido)

document.write(texto);
