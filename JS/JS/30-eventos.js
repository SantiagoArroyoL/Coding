'use strict'

//Eventos del ratón
/* Para HTML (onclick, ondbclick) */

/* Agragamos este evento por si no ha cargado todo el HTML
 * y no exista ningún error
window.addEventListener('load', () => {
	function cambiarColor() {
		var bg = boton.style.background;
		if (bg == "green") {
			boton.style.background = "red";
		} else {
			boton.style.background = "green";
		}
		boton.style.padding = "10px";
		boton.style.border = "1px solid #ccc";
	}

	var boton = document.querySelector("#boton");

	/* Click */
	boton.addEventListener('click',function() {
		cambiarColor();
		// boton.style.border = "10px solid black";
		this.style.border = "10px solid black";
	});
	/* Mouse Over */
	boton.addEventListener('mouseover',function(){
		boton.style.background = "#ccc"
	});
	/* Mouse Out */
	boton.addEventListener('mouseout',function(){
		boton.style.background = "black"
	});

	/* Focus */
	var input = document.querySelector("#campo_nombre");

	input.addEventListener('focus',function(){
		console.log("[focus] Estás dentro del input");
	}),
	/* Blur */
	input.addEventListener('blur',function(){
		console.log("[blur] Estás fuera del input");
	});

	// Teclado


	/* Keydown */
	input.addEventListener('keydown',function(event){
		console.log("Pulsando la tecla", String.fromCharCode(event.keyCode));
	});
	/* Keypress */
	input.addEventListener('keypress',function(event){
		console.log("Presionando la tecla", String.fromCharCode(event.keyCode));
	});
	/* Keyup */
	input.addEventListener('keyup',function(event){
		console.log("Soltando la tecla", String.fromCharCode(event.keyCode));
	});
}); //Final del load
