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
		var edad = parseInt(document.querySelector("#edad").value);

		if(nombre.trim() == null || nombre.trim().length == 0) {
			alert("El nombre no es válido");
			document.querySelector("#error_nombre").innerHTML = "El nombre no es válido"
			return false;
		} else {
			document.querySelector("#error_nombre").style.display = "none";
		}

		if(apellidos.trim() == null || apellidos.trim().length == 0) {
			alert("Los apellidos no es válido");
			return false;
		}
		if(edad == null || edad <= 0 || isNaN(edad)) {
			alert("La edad no es válida	");
			return false;
		}

		boxDashed.style.display = "block"

		var datosUsuario = [nombre, apellidos, edad];
		var indice;
		for (indice in datosUsuario) {
			var parrafo = document.createElement("p");
			parrafo.append(datosUsuario[indice]);
			boxDashed.append(parrafo);
		}
	});
});
