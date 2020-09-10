<!-- A poco PHP funciona con HTML?
     Bitch PHP es html  -->
<!DOCTYPE html>
<html lang="es" dir="ltr">
	<head>
		<meta charset="utf-8">
		<title>Curso PHP - 1</title>
	</head>
	<body>
		<?php
			$title = "Hecho por Santiago Arroyo Lozano!";
			// Este es un comentario
			/* Así también funciona, como en cualquier lenugaje */
		 ?>
		<h1>Hola mundo desde PHP!</h1>
		<h1><?php echo $title; ?></h1>
	</body>
</html>
