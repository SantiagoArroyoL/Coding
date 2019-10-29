'use strict'

//Pruebas con Let y Var


//Prueba con var
var numero = 40;
console.log(numero); //Valor 40

if (true) {
	var numero = 50;
	console.log(numero); //Valor 50

}


//Prueba con Let
var texto ="Curso de JS para trabajr";
console.log(texto);

if (true) {
	let texto = "Curso de JS para ser la verga"
	console.log(texto);
}

console.log(texto); //Var es una variable global y Let sólo funciona por bloque
