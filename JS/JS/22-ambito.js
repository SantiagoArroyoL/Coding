'use strict';
function holaMundo(texto){
	var hola_mundo = "Texto dentro de una función ";

	console.log(texto);
	console.log(hola_mundo);

}

var texto = "Hola mundo soy una variable global"
holaMundo(texto);
console.log(hola_mundo); //Hola mundo sólo está definida en la función, por eso no sirve
