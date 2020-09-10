<?php include 'functions.php'; ?>
<?php if (isset($_POST['submit'])){ deleteRow(); } ?>
<!--En este archivo es un login - solo borramos de la base de datos -->
<!doctype html>
<html lang="es">
<head>
    <meta charset="UTF-8">
    <meta name="viewport"
          content="width=device-width, user-scalable=no, initial-scale=1.0, maximum-scale=1.0, minimum-scale=1.0">
    <meta http-equiv="X-UA-Compatible" content="ie=edge">
    <title>Document</title>
    <link rel="stylesheet" href="https://stackpath.bootstrapcdn.com/bootstrap/4.5.2/css/bootstrap.min.css" integrity="sha384-JcKb8q3iqJ61gNV9KGb8thSsNjpSL0n8PARn9HuZOnIxN0hoP+VmmDGMN5t9UJ0Z" crossorigin="anonymous">
    <script src="https://stackpath.bootstrapcdn.com/bootstrap/4.5.2/js/bootstrap.min.js" integrity="sha384-B4gt1jrGC7Jh4AgTPSdUtOBvfO8shuf57BaghqFfPlYxofvL8/KUEfYiJOMMV+rV" crossorigin="anonymous"></script>
</head>
<body>
<div class="container">
    <h1>Delete</h1>
    <div class="col-sm-6">
        <form action="login_delete.php" method="post">
            <div class="form-group">
                <select name="id" id="">
<!--mostramos el indice de los usuarios para que elijan cual borrar-->
                    <?php showUsers(); ?>
                </select>
            </div>
            <input type="submit" class="btn btn-primary" name="submit" value="DELETE">
        </form>
    </div>
</div>
</body>
</html>
