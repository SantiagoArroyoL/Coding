<?php include "functions.php"; ?>
<?php include "includes/header.php";?>
	<section class="content">

		<aside class="col-xs-4">
		<?php Navigation();?>


		</aside><!--SIDEBAR-->


<article class="main-content col-xs-8">


	<?php


	/*

	Step1: Use a pre-built math function here and echo it


	Step 2:  Use a pre-built string function here and echo it


	Step 3:  Use a pre-built Array function here and echo it

 	*/

	//1
	echo pow(2,64);
	echo "<br>";
	//2
	echo strlen("Santiago");
	echo "<br>";
	//3
	$arr = ["hola","adios","Santiago","anita lava la tina"];
	echo sort($arr);
?>





</article><!--MAIN CONTENT-->
<?php include "includes/footer.php"; ?>
