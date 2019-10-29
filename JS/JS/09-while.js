'use strict'


//Bucle while

var year = 2018;

while(year != 1991) {
	console.log("Estamos en el año " + year);

	if (year == 2000) {
		break;
		//Interrumpe el bucle cuando llega a 2000, antes de que llegue a 2018 evidentemente	
	}

	year--;
}

//Do while

var years = 30;

do {
	alert("SOLO CUANDO SEA DIFERENTE A 20");
	years--;
} while (years > 25);

//BREAK, romper un bucle
