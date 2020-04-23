'use strict'

// Localstorage

// Comprobar disponibilidad de Localstorage
if (typeof(Storage) != 'undefined') {
	console.log("Localstorage disponible");
} else {
	console.log("Incompatible con Localstorage");
}

// Guardar datos
localStorage.setItem("titulo", "Curso de JS Santiago Arroyo");

// Recuperar elemento
// console.log(localStorage.getItem("titulo"));
document.querySelector("#peliculas").innerHTML = localStorage.getItem("titulo");

// Guardar objetos
var usuario = {
	nombre: "Santiago Arroyo",
	email: "santiago@arroyo.com",
	web: "santiago.com"
};
/* JS no permite añadir objetos de forma nativa al localStorage
 * Lo que hacemos entonces es hacerlo una cadena de JSON
*/
localStorage.setItem("usuario", JSON.stringify(usuario));

// Recuperar objeto
var user = JSON.parse(localStorage.getItem("usuario"));
/* Parse JSON porque está guardado su valor en cadena, no su valor JSON */
console.log(user);
document.querySelector("#datos").append(" " + user.web + " - " + user.nombre);

// Eliminar de localStorage
localStorage.removeItem("usuario");

// Vacía el localStorage
localStorage.clear():
