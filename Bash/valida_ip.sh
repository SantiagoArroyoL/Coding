#!/bin/bash

# Función auxiliar para verificar si una IP es válida en el contexto de octetos
es_ip_valida() {
    local ip=$1
    local IFS='.'
    read -r -a octetos <<< "$ip"

    # Verificar que hay exactamente 4 octetos
    if [ ${#octetos[@]} -ne 4 ]; then
        return 1
    fi

    for octeto in "${octetos[@]}"; do
        # Verificar si el octeto está vacío o si contiene caracteres no numéricos
        # Verificar si el octeto tiene ceros al principio o si excede 255
        if [[ -z $octeto ]] || [[ ! $octeto =~ ^[0-9]+$ ]] || [[ $octeto -gt 255 ]] || [[ $octeto =~ ^0[0-9]+ ]]; then
            return 1
        fi
    done

    return 0
}

# Verificar si se proporcionó una IP
if [ "$#" -ne 1 ]; then
    echo "Uso: $0 <dirección_ip>"
    exit 1
fi

ip=$1

# Verificar si la IP es válida
if ! es_ip_valida "$ip"; then
    echo "La IP $ip es inválida."
    exit 1
fi

# Determinar si la IP es privada, de autoreconocimiento o autoasignada
if [[ $ip =~ ^127\.0\.0\.([1-9]|1[0-9]{2}|2[0-4][0-9]|25[0-4])$ ]]; then
    echo "La IP $ip es válida y es de autoreconocimiento."
elif [[ $ip =~ ^169\.254\..*$ ]]; then
    echo "La IP $ip es válida y es autoasignada por error."
elif [[ $ip =~ ^(10\.|172\.(1[6-9]|2[0-9]|3[0-1])\.|192\.168\.) ]]; then
    echo "La IP $ip es válida y es privada."
else
    echo "La IP $ip es válida y es pública."
fi

exit 0

