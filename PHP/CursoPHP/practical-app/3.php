<?php include "functions.php"; ?>
<?php include "includes/header.php";?>

	<section class="content">

	<aside class="col-xs-4">

	<?php Navigation();?>

	</aside><!--SIDEBAR-->


<article class="main-content col-xs-8">

<?php

	/*  Step1: Make an if Statement with elseif and else to finally display string saying, I love PHP



		Step 2: Make a forloop  that displays 10 numbers


		Step 3 : Make a switch Statement that test againts one condition with 5 cases

	*/

	//1
	if (3 > 5) {
		// code...
	} else if (5 > 6) {
		// code...
	} else {
		echo "I love PHP<br>";
	}
	//2
	for ($i=1; $i < 11; $i++) {
		echo $i;
	}
	echo "<br>";
	//3
	switch ($i) {
		case 1: echo "Yay"; break;
		case 2: echo "Yay"; break;
		case 3: echo "Yay"; break;
		case 4: echo "Yay"; break;
		case 11: echo "Yay"; break;
		default: echo "noYay"; break;
	}





?>






</article><!--MAIN CONTENT-->

<?php include "includes/footer.php"; ?>
