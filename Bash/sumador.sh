#!/bin/bash

for number in "$@"
do
    #Regex pa verificar que sean números y evitar errores
    if [[ ! $number =~ ^-?[0-9]+?$ ]]; then
	    echo "Error! Todos los valores deben ser números enteros."
	    exit 1
    fi
    sum=$((sum + number))
done

echo "El resultado es: $sum"
