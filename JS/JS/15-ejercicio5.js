'use strict';

//Muestre todos los numeros de divisores de un numero introduce en prompt

var numero = parseInt(prompt('Mete un numero'));

for (var i = 0; i <= numero; i++) {

	if (numero%i == 0) {
		
		console.log('Divisor ' + i);
	}
}
