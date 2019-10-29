'use strict'

//var switch

var edad = 41;
var imprime = "";

switch (edad) {
	case 18:
		imprime = "Acabas de cumplir la mayoría de edad";
	break;
	case 25:
		imprime = "Ya eres un adulto";
	break;
	case 40:
		imprime = "Crisis de los 40";
	break;
	case 75:
		imprime = "Perteneces ya a la tercera edad";
	break;
	default:
		imprime = "Tu edad es neutra";
	break;
}	
console.log(imprime);
