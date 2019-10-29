use strict;







//Conseguir elementos con un ID concreto

//var caja = document.getElementById("micaja");
var caja = document.querySelector("#micaja");

caja.innerHTML = "!TEXTO EN  LA CAJA DESDE JS!";
caja.style.background = "red";
caja.style.padding = "20px";
caja.style.color = "white";
caja.className = "hola hola2";

//Conseguir elemntos por su etiqueta
var todosLosDivs = document.getElementsByTagName('div');

todosLosDivs.forEach((valor, indice) => {
	var parrafo = document.createElement("p");
	var texto = document.createTextNode(valor);
	parrafo.appendChild(texto);
	document.querySelector("#miseccion").appendChild(parrparrafo);
});

console.log(contenidoEnTexto);

//Conseguir elementos por su clase css
