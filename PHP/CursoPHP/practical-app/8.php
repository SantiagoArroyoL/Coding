<?php include "functions.php"; ?>
<?php include "includes/header.php";?>

	<section class="content">

		<aside class="col-xs-4">

		<?php Navigation();?>
			
			
		</aside><!--SIDEBAR-->


		
	<article class="main-content col-xs-8">
	
	
	<?php  

	/*
	    Step 1 -Make a variable with some text as value

		Step 2 - Use crypt() function to encrypt it

		Step 3 - Assign the crypt result to a variable

		Step 4 - echo the variable
	*/
    //1
    $texto = "mucho texto";
    //2
    $mascara = "PA!/&%$#vdfññññsvsvg123843";
    //3
    $variable_final = crypt($texto, $mascara);
    //4
	echo $variable_final;
	?>





</article><!--MAIN CONTENT-->
<?php include "includes/footer.php"; ?>