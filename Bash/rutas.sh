#!/bin/bash

# Solicitamos la ruta
read -p "Ingresa una ruta por favor: " ruta

if [ -e "$ruta" ]; then
  echo "1. El archivo o directorio existe."
  
  # Determinar el tipo de archivo
  tipo=$(file -b "$ruta")
  echo "2. Tipo de archivo: $tipo"

  echo "3. El archivo: "
  
  if [ -r "$ruta" ]; then
    echo "    Se puede leer."
  fi
  
  if [ -w "$ruta" ]; then
    echo "    Se puede escribir."
  fi
  
  if [ -x "$ruta" ]; then
    echo "    Se puede ejecutar."
  fi
else
  echo "El archivo o directorio no existe."
fi

