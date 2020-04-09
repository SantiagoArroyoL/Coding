'use strict';

// BOM -Browser Objetct Model

/* Así se ve la ventana del navegador */
console.log(window.innerHeight);
console.log(window.innerWidth);

/* Valores del sistema */
console.log(window.screen.width);
console.log(window.screen.height);
console.log(window.location);

/* Modifica el href de la pestaña actual (Abre la nueva página en esta misma pestaña) */
function redirect(url) {
	window.location.href = url;
}

/* Abre en pestaña nueva o incluso ventana nuevaa*/
function abrirVentana(url) {
	// window.open(url);
	window.open(url,"","width=400,height=300");
}
