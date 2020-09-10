<!DOCTYPE html>
<html lang="es" dir="ltr">
	<head>
		<meta charset="utf-8">
		<title>FUNCIONES BUILT-IN PHP</title>
	</head>
	<body>
		<!-- FUNCIONES MATEMATICAS -->
		<h1>MATES</h1>
		<?php
			echo pow(2,8); // 2 elevado a la 8
			echo "<br>";
			echo rand(1,100); // número aleatorio entre 1 y 100
			echo "<br>";
			echo sqrt(25); // raíz cuadrada
			echo "<br>";
			echo ceil(4.6);
			echo "<br>";
			echo floor(4.6);
			echo "<br>";
			echo round(4.4) . " ó " . round(4.6);
		?>
		<!-- FUNCIONES SOBRE STRING'S -->
		<h1>STRINGS</h1>
		<?php
			$string = "Lorem ipsum dolor sit amet, consectetur adipisicing elit.";
			echo strlen($string); // longitud de la cadena
			echo "<br>";
			echo strtoupper($string);
			echo "<br>";
			echo strtolower($string);
			echo "<br>";
			printf($string);
		?>
		<!-- FUNCIONES SOBRE ARREGLOS -->
		<h1>ARREGLOS</h1>
		<?php
			$list = [2,3,4,5,6,7,8,9,10,1,.3];
			print_r($list); // imprime todo el arreglo
			echo "<br>";
			echo max($list); // elemento más grande en el arreglo (de mayor orden)
			echo "<br>";
			echo min($list); // elemento más pequeño en el arreglo (de menor orden)
			echo "<br>";
			sort($list); // ordena el arreglo
			print_r($list);
		?>
	</body>
</html>
