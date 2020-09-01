<!DOCTYPE html>
<html lang="es" dir="ltr">
	<head>
		<meta charset="utf-8">
		<title></title>
	</head>
	<body>
		<?php
			// Funciona exactamente como cualquier if

			if (3 > 5) {
				// code...
			} else if (4 < 1) {
				// code...
			} else {
				// code...
			}
		?>
		<!-- El if embeded con html por el otro lado es más interesante
	 		Puedes definir qué estructuras de html quieres que se ejecuten o no -->
		<?php if (3 > 5): ?>
			<h1>En primer if</h1>
		<?php else: ?>
			<h1>En else</h1>
		<?php endif; ?>

		<?php
			// Los operadores lógicos y de comparación son iguales en PHP:

			/*
			Mayor que >
			Menor que <
			Igual ==
			Negacion !
			No igual !=
			AND &&
			OR ||

			NUEVOS:
			and (AND)
			or (OR)
			xor (XOR)
			No igual <>   (Funciona igual)
			Identico === (Iguales y del mismo tipo)
			No identico !== (Ver ejemplo)
			Spaceship <==> (Funciona como el comparator en Java, ejemplo más adelante)

			*/
			if (4 == "4") {
				echo "WHAT<br>";
			}
			if (4 !== "4") {
				echo "Qué loco no?<br>";
			}
			// El if sin parámetros es literalmente un if de existencia, pregunta si fue iniciada o no
			$temp = 1;
			if ($temp) {
			    echo "La variable temp fue inicializada";
            }

			// Así funcionan los comparator y las spaceship:
			$x = 5;
			$y = 10;

			echo ($x <=> $y); // returns -1 because $x is less than $y
			echo "<br>";

			$x = 10;
			$y = 10;

			echo ($x <=> $y); // returns 0 because values are equal
			echo "<br>";

			$x = 15;
			$y = 10;

			echo ($x <=> $y); // returns +1 because $x is greater than $y
			echo "<br>";

			/* SWITCH */
			$number = 4;
			switch ($number) {
				case 4:
					echo "Se logró";
					break;
				case 5: echo "misma linea"; break;
				case 6: {
					echo "Mira, con llavecitas también (Se constante)";
					break;
				}
				default:
					echo "No se logró";
					break;
			}

			/* LOOPS */
			// While
			echo "<h1>LOOPS:</h1>";
			$x = 20;
			while ($x >= 10) {
				//Nótese lo raro que es trabajr con cadenas en PHP
				echo "El valor de x: $x <br>";
				$x--;
			}

			// For
			for ($i=0; $i < 10; $i++) {
				echo "<h2>Estamos en el for loop: " . $i . "</h2><br>";
			}

			// For-each
			$collection = [1,2,3,4,"Yay"];
			foreach ($collection as $number) {
				echo "Yuju $number ";
			}
			echo "<br>";
			// nani, self explanatory:
			foreach ($collection as $key => $number) {
				// En este caso la key es el indice porque es un arreglo
				// Si fuera asociativo u otra coleccion pues cambia la cosa
				echo "La llave es: $key y el número es: $number <br>";
			}
		?>
	</body>
</html>
