<?php

include 'Car.php';

if (class_exists("Car")) {
    echo "Existe el auto";
    if (method_exists("Car","move")) {
        echo "y se puede mover<br>";
    } else {
        echo "y no se puede mover<br>";
    }
} else {
    echo "No existe el coche<br>";
}
$bmw = new Car();
/* Por alguna extraña razón en vez de usar el punto usan una flecha para acceder a los métodos del objeto */
$bmw->move();
$bmw->setWheels(12);
echo $bmw->getWheels();
