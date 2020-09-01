<?php
/* Hacemos la conexión */
$connection = mysqli_connect('localhost','root','','loginapp');
if (!$connection) {
    die("Hubo un error al conectarse a la base de datos por favor espere");
}
?>
