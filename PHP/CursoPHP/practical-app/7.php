<?php include "functions.php"; ?>
<?php include "includes/header.php";?>
    

	<section class="content">

		<aside class="col-xs-4">

		<?php Navigation();?>
			
			
		</aside><!--SIDEBAR-->


	<article class="main-content col-xs-8">
	
	
	
	<?php  

	/*
	    Step 1 - Create a database in PHPmyadmin

		Step 2 - Create a table like the one from the lecture

		Step 3 - Insert some Data

		Step 4 - Connect to Database and read data
    */

    //1 y 2
    /* La base de datos se llama "practica7" y la única tabla que tiene se llama "usuarios"
     * Las tres columnas son 1.-id 2.-nombre 3.-contra                             */
    //3 - La voy a insertar por aquí porque el punto es practicar PHP y MySQL imbécil
    /* Hacemos la conexión */
    $connection = mysqli_connect('localhost','root','','practica7');
    if (!$connection) {
        die("Hubo un error al conectarse a la base de datos por favor espere");
    }
    /* Creamos el string con el query y se lo pedimos a la base */
    $query = "INSERT INTO usuarios(nombre,contra) ";
    $query .= "VALUES ('Andrés Patiño','TioPatito123')";
    $result = mysqli_query($connection,$query);
    /* Si algo falla pues avisamos */
    if (!$result) {
        die("No se pudo escribir a la base");
    }

    //4 - a leer
    $inQuery = "SELECT * FROM usuarios";
    $resultOut = mysqli_query($connection,$inQuery);
    while ($row = mysqli_fetch_assoc($resultOut)) {
        echo "<pre>";
        print_r($row);
        echo "<br>";
        echo "</pre>";
    }
	?>





</article><!--MAIN CONTENT-->

<?php include "includes/footer.php"; ?>
