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
