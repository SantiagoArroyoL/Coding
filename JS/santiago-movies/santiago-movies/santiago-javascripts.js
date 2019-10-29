// document ready
$(document).ready(function() {
	//alert('document ready');
});

// VARIABLES GLOBALES
var peliculas = [];

// addMovie
function addMovie(){

	// alert('addMovie');
	var form_valid = true;
	var errors = [];

	if ($('#pelicula_name').val() == '' || $('#pelicula_name').val().length<1) {
		form_valid = false;
		$('#pelicula_name').focus()
		errors.push('pelicula_name');
		fieldError('#pelicula_name');
	} else {
		fieldCorrect('#pelicula_name');
		peliculas.push($('#pelicula_name').val() );
	}
	// pelicula_name
	$('#pelicula_name').val("");
}
// viewMovies
function updateViewMovies(){

	console.log('updateViewMovies -> peliculas -> ');
	console.log(peliculas);

	var peliculas_cards = "";

	peliculas.forEach(function(pelicula) {
	    console.log(pelicula);
		pelicula_card = '<li class="list-group-item">' + pelicula + '</li>';
	    console.log(pelicula_card);
	    peliculas_cards = peliculas_cards + pelicula_card;
	});

	$("#movies_list").html(peliculas_cards);
}

// ********************************************************************************
// fieldError
// ********************************************************************************
function fieldError(fieldName) {
	$(fieldName).css({"border-bottom":"2px solid #950044"});
	// 	stringToUppercase(fieldName);
} // fieldCorrect

// ********************************************************************************
// fieldCorrect
// ********************************************************************************
function fieldCorrect(fieldName) {
	$(fieldName).css({"border-bottom":"1px solid #CED4DA"});
	// 	stringToUppercase(fieldName);
} // fieldCorrect
