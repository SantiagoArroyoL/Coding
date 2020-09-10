<?php


class SuperCar extends Car {
    public function __construct(string $name) {
        parent::__construct(100, $name);
    }
}