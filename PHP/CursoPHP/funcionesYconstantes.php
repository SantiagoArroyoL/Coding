<!DOCTYPE html>
<html lang="es" dir="ltr">
	<head>
		<meta charset="utf-8">
		<title></title>
	</head>
	<body>
		<?php
		/* Just like that hicimos una función */
			function helloWorld() {
				echo "Hello World!<br>";
			}
			helloWorld();
			/* Con parámetros y valore de retorno y todo */
			function suma($a,$b) {
				return $a+$b;
			}
			echo suma(1,2) . "<br>";
			/* Las constantes se definen así: */
			define("NAME",100);
			define('ANIMALS', array('dog','cat','bird'));
			print_r(ANIMALS);//No se necesita el signo de pesos

			/* O esta forma, pero no funciona en todos los PHP: */
			// const ANIMALES = array('dog','cat'00);
			// const NOMBRE = "Santiago";
			
		?>
	</body>
</html>
