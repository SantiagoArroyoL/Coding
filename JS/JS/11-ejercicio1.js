'use strict'


/*Programa que pida dos numeros y que nos diga cual es el mayor, el menor y si son iguales
PLUS: Sólo te permite meter números
*/

var numero1 = parseInt(prompt('Introduce el primer numero'));
var numero2 = parseInt(prompt('Introduce el segundo numero'));

//Este while es el "PLUS" del ejercicio 1
while(numero1 <= 0 || numero2 <=0 || isNan(numero1) || isNan(numero2)){
	 numero1 = parseInt(prompt('Introduce el primer número'));
	 numero2 = parseInt(prompt('Introduce el segundo número'));
}

 if (numero1 == numero2) {
	alert('LOS NÚMEROS SON IGUALES');
}
else if (numero1 > numero2) {
	alert('El número mayor es ' + numero1);
}
else if(numero1 < numero2){
	alert('El número mayor es ' + numero2);
}
else{
	alert('Introduce números correctos');
}
