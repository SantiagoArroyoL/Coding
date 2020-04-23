"use strict";

// Fetch (ajax) y peticiones a servicios / apis rest

var divUsuarios = document.querySelector("#usuariosDiv");

fetch('https://jsonplaceholder.typicode.com/users')
	.then(data => data.json())
	.then(data => {

		// console.log("Data:");
		// console.log(data);
		printUsuarios(data);


		// usuarios.map((user, i) => {

		// });
	});

function printUsuarios(usuarios) {
	console.log("usuarios");
	console.log(usuarios);

	usuarios.forEach(usuario => {
		console.log(usuario.name);
		let nombre = document.createElement('h3');
		nombre.innerHTML = usuario.name;
		divUsuarios.appendChild(nombre);
	});
	setTimeout(function () {
		document.getElementById("loadingDiv").style["display"] = "none";
		document.getElementById("usuariosDiv").style["display"] = "block";
    }, 3000);
}
