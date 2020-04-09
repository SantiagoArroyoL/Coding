'use strict';

//Conseguir elementos con un ID concreto

/* La primera opción puede no funcionar puesto que si el elemento se carga despues de el archivo JS en HTML no va a existir*/
//var caja = document.getElementById("micaja");
var caja = document.querySelector("#micaja");

caja.innerHTML = "!TEXTO EN  LA CAJA DESDE JS!";
caja.style.background = "red";
caja.style.padding = "20px";
caja.style.color = "white";
caja.className = "hola hola2";

//Conseguir elemntos por su etiqueta
var todosLosDivs = document.getElementsByTagName('div');

var seccion = document.querySelector("#miseccion");
var hr = document.createElement("hr");

/* El for each no funciona con HTML Collections */
// todosLosDivs.forEach((valor, indice) => {});
for (var valor in todosLosDivs) {
	if (typeof todosLosDivs[valor].textContent == 'string') {
		var parrafo = document.createElement("p");
		var texto = document.createTextNode(todosLosDivs[valor].textContent);
		parrafo.append(texto);
		seccion.append(parrafo);
	}
}
seccion.append(hr);

//Conseguir elementos por su clase css 
var divsRojos = document.getElementsByClassName('rojo');
var divAmarillo = document.getElementsByClassName('amarillo');
divAmarillo[0].style.background = "yellow";

for (var div in divsRojos) {
	if (divsRojos[div].className == "rojo") {
		divsRojos[div].style.background = "red";
	}
}

//Query Selector
var id = document.querySelector("#encabezado");
console.log(id);

var claseRojo = document.querySelector("div.rojo");
console.log(claseRojo);

var etiqueta = document.querySelector("div");
console.log(etiqueta);
