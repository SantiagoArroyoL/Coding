<?php


class Car {

    public int $wheels;
    public string $name;

    /**
     * Car constructor.
     * @param int $wheels
     * @param string $name
     */
    public function __construct(int $wheels, string $name) {
        $this->wheels = $wheels;
        $this->name = $name;
    }

    /**
     * @return mixed
     */
    public function getWheels() {
        return $this->wheels;
    }

    /**
     * @param mixed $wheels
     */
    public function setWheels($wheels) {
        $this->wheels = $wheels;
    }

    public function move() {
        echo "Me estoy moviendo";
    }
}