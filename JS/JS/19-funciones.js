'use strict';

//Funciones
//Una función es una grupación reutilizable de un conjunto de instrucciones

//Defino la función, con parámetros
function calculadora(numero1, numero2, mostrar = false){ //Mostrar es un parámetro opcional, no pasa nada si no se pone porque ya tiene un valor por default

	//Conjunto de instrucciones a ejecutar

	if (mostrar == false) {
		console.log("Suma " + (numero1+numero2));
		console.log("Resta " + (numero1-numero2));
		console.log("Multiplicación " + (numero1*numero2));
		console.log("División " + (numero1/numero2));
		console.log("************************************");
	}else {
		document.write("Suma " + (numero1+numero2) +"<br>");
		document.write("Resta " + (numero1-numero2) +"<br>");
		document.write("Multiplicación " + (numero1*numero2) +"<br>");
		document.write("División " + (numero1/numero2) +"<br>");
		document.write("************************************<br>");
	}

	return "Hola soy la calculadora" //(Aquí sí requiere el console log aparte)
}

//Invocar o llamar a la función
calculadora(1,4);
calculadora(6,4,true);
/* Método 2
calculadora(12,8);
calculadora(98,2);
console.log("DEL 0 AL 10");

for (var i = 0; i <= 10; i++) {
	console.log(i);
	calculadora(i,8)
}*/
