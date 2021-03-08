# -*- coding: utf-8 -*-
"""
Created on Wed Feb  3 14:07:42 2021

@author: santi
"""
import sys
if len(sys.argv) != 2:
    sys.exit("No introduciste ningún parámetro!\n Ejemplo: descomposicion.py 1")

x = int(sys.argv[1])
if x < 1:
    sys.xit("Introduce sólo enteros positivos por favor")
    
    cadena = str(x)
    longitud = len(cadena)

    for i in range(longitud):
        print( "{:04d}".format( int(cadena[longitud-1-i]) * 10 ** i ))
