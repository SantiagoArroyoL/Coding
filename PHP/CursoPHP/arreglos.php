<!DOCTYPE html>
<html lang="es" dir="ltr">
	<head>
		<meta charset="utf-8">
		<title></title>
	</head>
	<body>
		<?php
			$name = "<h1>Santiago";

			// Esta falacia de aqui es para concatenar: (El + no concatena)
			echo $name . " Arroyo</h1>";

			// Oh y por supuesto se pueden hacer operaciones en PHP
 		   echo 2+2/2; //  3
		   echo "<br><br><br>";

		   // Y pero si por supuesto hay arreglos!
		   $numberList = array("Hola",2 ,3 ,4); //Maldita sea no son homogeneos
		   // Pero también los puedes crear como siempre:
		   $arreglo = ["Adios",4,6.7,8];

		   // Podemos hacer echo de los elemtnso del arreglo (No del arreglo completo)
		   echo $numberList[0];
		   // La función de PHP llamada print_r es la que imprime todo el arreglo
		   echo "<br><br><br>";
		   print_r($arreglo);

		   echo "<br><br><br>";
		   /* Arreglos asociativos */
		   $arregloAsoc = ["Nombre" => "Santiago", "Apellidos" => 'Arroyo Lozano'];
		   print_r($arregloAsoc);
		   echo "<h1>" . $arregloAsoc["Nombre"] . "<h1>";
		   // $arregloAsoc[0] no funciona ya que no existe
		?>
	</body>
</html>
