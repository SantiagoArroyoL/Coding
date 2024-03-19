#!/bin/bash

if [ ! -f "$1" ]; then
	echo "El archivo no existe!"
	exit 1
fi

n_lineas=$(wc -l < "$1")

for (( i=$n_lineas; i>0; i-- )); do
	# Imprime la i-ésima línea. Head nos da hasta la linea i, despues obtenemos la ultima linea de la salida de head. (la i-ésima linea)
    head -n $i "$1" | tail -n 1
done
