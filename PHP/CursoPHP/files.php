<?php
/* Creemos un nuevo archivo llamado example.txt */
$file = "example.txt";
$handle = fopen($file,'w'); // Esto crea el archivo como tal
fclose($handle);

/* Vamos a escribir al archivo */
if ($handle = fopen($file,'w')) {
    fwrite($handle,"I LOVE PHP"); //Escribimos
    fclose($handle);
} else {
    echo "No pudimos escribir al archivo";
}

/* Vamos a leer el archivo */
if ($handle = fopen($file,'r')) {
//    echo $content = fread($handle,2); //Leemos (cada byte es un caracter)
    echo $content = fread($handle,filesize($file)); //Leemos ( cada byte es un caracter)
    fclose($handle);
} else {
    echo "No pudimos leer el archivo";
}

/* Y para borrarlo sólo es necesario una función */
//unlink("example.txt");