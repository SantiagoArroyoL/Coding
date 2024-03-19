#!/bin/bash

directorio=$1
if [ ! -d "$directorio" ]; then
    echo "El argumento proporcionado no es un directorio o no existe!"
    exit 1
fi

# Array asociativo para almacenar los hashes de los archivos
declare -A hashes

# Busca archivos y calcula su hash
while IFS= read -r archivo; do
    # Ignora los directorios
    if [ -f "$archivo" ]; then
        # Calcula el hash del archivo
        hash=$(md5sum "$archivo" | awk '{ print $1 }')

        # Almacena en el array asociativo
        hashes[$hash]+="$archivo "
    fi
done < <(find "$directorio" -type f)

copias="./copias"
archivo_duplicados="duplicados.txt" > "$archivo_duplicados"

mkdir -p "$copias"

for hash in "${!hashes[@]}"; do
    archivos=${hashes[$hash]}
    read -r -a arr <<< "$archivos"
    if [ ${#arr[@]} -gt 1 ]; then
        echo "Archivos duplicados:"
        for a in "${arr[@]}"; do
            echo "  $a"
	    mv "$a" "$copias" 
            echo "$a" >> "$archivo_duplicados"
        done
        echo "" >> "$archivo_duplicados"
    fi
done 
echo "Terminado"

