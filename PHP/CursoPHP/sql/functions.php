<?php include 'db.php';

/**
 * Función que muestra el indice de cada usuario y la pone dentro de un <selection>
 */
function showUsers() {
    global $connection;
    $outQuery = "SELECT * FROM users";
    $result = mysqli_query($connection,$outQuery);
    if (!$result) {
        die("Query failed!" . mysqli_error($connection));
    }
    while ($row =mysqli_fetch_assoc($result)) {
        $id = $row['id'];
        echo "<option value='$id'>$id</option>";
    }
}

/**
 * Función que encripta un string recibida basado en una máscara predefinida
 * @param $string La cadena a encriptar
 */
function encripta($string) {
    $mascara = "PA!/&%$#vdfññññsvsvg123843";
    return crypt($string, $mascara);
}

/**
 * Función que actualiza una fila seleccionada
 */
function updateTable() {
    global $connection;
    $username = mysqli_real_escape_string($connection, $_POST['username']);
    $weak_password = mysqli_real_escape_string($connection, $_POST['password']);
    $id = $_POST['id'];

    $password = encripta($weak_password);

    $query = "UPDATE users SET ";
    $query .= "username = '$username', ";
    $query .= "password = '$password' ";
    $query .= "WHERE id = $id "; //Es un int en la base de datos

    $result = mysqli_query($connection,$query);
    if (!$result) {
        die("Query failed!" . mysqli_error($connection));
    }
}

/**
 * Función que borra una fila seleccionada
 */
function deleteRow() {
    global $connection;
    $id = $_POST['id'];

    $query = "DELETE FROM users ";
    $query .= "WHERE id = $id "; //Es un int en la base de datos

    $result = mysqli_query($connection,$query);
    if (!$result) {
        die("Query failed!" . mysqli_error($connection));
    }
}

/**
 * Función que añade una fila a la tabla
 */
function addRow() {
    global $connection;
    $username = mysqli_real_escape_string($connection, $_POST['username']);
    $weak_password = mysqli_real_escape_string($connection, $_POST['password']);
    $password = encripta($weak_password);

    if ($connection) {
        echo "We are connected<br>";
    } else {
        die("Hubo un error al conectarse a la base de datos por favor espere");
    }

    $query = "INSERT INTO users(username,password) ";
    $query .= "VALUES ('$username','$password')";

    $result = mysqli_query($connection,$query);

    if (!$result) {
        die("Query failed");
    }
}

/**
 * Muestra el arreglo asociativo de cada tabla y lo imprime con <pre>
 */
function showTable() {
    global $connection;
    $outQuery = "SELECT * FROM users";
    $resultOut = mysqli_query($connection,$outQuery);
    while ($row = mysqli_fetch_assoc($resultOut)) {
        echo "<pre>";
        print_r($row);
        echo "<br>";
        echo "</pre>";
    }
}

/**
 * Esta es una función de dispersión avanzada, muy buena para encripitar
 * El único problema de usarla es que como todos saben de sus existencia todos saben desencriptarla jeje
 * Pero primero deberían saber qué estas encriptando con Bob Jenkins (Así se llama la función) y eso es más dificil
 * Hasta cierto punto es mejor usar crypt() como en el otro método
 * Sólo dejo esto por diversión, fue muy fácil pasarla de Java a PHP
 * @param $key La llave para definir la encripción
 * @return string La cadena a encriptar
 */
function jenkins_hash($key) {
    $key = (string)$key;
    $len = strlen($key);
    for($hash = $i = 0; $i < $len; ++$i) {
        $hash += ord($key[$i]);
        $hash += ($hash << 10);
        $hash ^= ($hash >> 6);
    }
    $hash += ($hash << 3);
    $hash ^= ($hash >> 11);
    $hash += ($hash << 15);
    //dechex pasa de decimal a hexadecimal - str_pad transforma de número a string
    return str_pad(dechex($hash),16,0,STR_PAD_LEFT);
}
