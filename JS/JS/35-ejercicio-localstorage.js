'use strict'

var formulario = document.querySelector("#formpeliculas");

formulario.addEventListener('submit', ()=>{
	var titulo = document.querySelector("#addpelicula").value;
	if (titulo.length > 0) {
		localStorage.setItem(titulo, titulo);
	}
});

var ul = document.querySelector("#peliculas-list");
for (var i in localStorage) {
	console.log(localStorage[i]);
	if (typeof localStorage[i] == 'string') {
		var li = document.createElement("li");
		li.append(localStorage[i]);
		ul.append(li);
	}
}

var formulariob = document.querySelector("#formBorrarPeliculas");

formulariob.addEventListener('submit', ()=>{
	var titulo = document.querySelector("#rempelicula").value;
	if (titulo.length > 0) {
		localStorage.removeItem(titulo);
	}
});
