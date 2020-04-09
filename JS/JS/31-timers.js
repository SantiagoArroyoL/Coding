'use strict'

window.addEventListener('load', () => {
	//Timers
	// var tiempo = setTimeOut(() => {
	/* Time out se ejecuta una vez y muere, set interval lo repite */
	function intervalo() {
		var tiempo = setInterval(() => {
			console.log("Set interval ejecutando");
			var encabezado = document.querySelector("h1");
			if (encabezado.style.fontSize == "50px") {
				encabezado.style.fontSize = "30px";
			} else {
				encabezado.style.fontSize = "50px";
			}
		}, 800);
		return tiempo;
	}

	var tiempo = intervalo();

	/* Ejemplo de cómo un botón detiene el intervalo */
	var stop = document.querySelector("#stop");
	stop.addEventListener('click', () => {
		alert("Has parado el intervalo en bucle");
		clearInterval(tiempo);
	});
	/* Iniciar el intervalo */
	var start = document.querySelector("#start");
	start.addEventListener('click', () => {
		alert("Has iniciado el intervalo en bucle");
		intervalo();
	});
});
