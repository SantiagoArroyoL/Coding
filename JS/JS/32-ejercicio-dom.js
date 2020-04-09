'use strict'

window.addEventListener('load', ()=>{
	console.log("DOM cargado");

	var formulario = document.querySelector("#formulario");
	var boxDashed = document.querySelector(".dashed");
	boxDashed.style.display = "none"

	formulario.addEventListener('submit', ()=>{
		console.log("Evento submit capturado");

		var nombre = document.querySelector("#nombre").value;
		var apellidos = document.querySelector("#apellidos").value;
		var edad = document.querySelector("#edad").value;

		boxDashed.style.display = "block"
		console.log(nombre, apellidos, edad);
	});
});
