<?php
    $nombres = ["Juan","Agus","German","Andres","Karina","Natalia","Sofi","Rosa"];
    if (isset($_POST['submit'])) {
        $user = $_POST['usuario'];
        $password = $_POST['contrasena'];
        if (strlen($user) < 5) {
            echo "YOU BITCH";
            exit;
        }
        if (in_array($user,$nombres)) {
            echo "YOU BITCH YA ESTAS AQUI";
            exit; // Salimos del php para que no cargue el resto de la página
        }
        // You get the idea
        echo "Tu usuario es: " . $user . "<br>";
        echo "Tu contraseña es: " . $password . "<br>";
    }
?>
<!DOCTYPE html>
<html lang="es" dir="ltr">
	<head>
		<meta charset="utf-8">
		<title></title>
	</head>

	<body>
		<form action="form.php" method="post">
			<input type="text" name="usuario" placeholder="Enter Username">
			<input type="password" name="contrasena" placeholder="Enter password">
			<br>
			<input type="submit" name="submit">
		</form>
	</body>
</html>
