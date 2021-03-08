# -*- coding: utf-8 -*-
"""
Created on Wed Feb  3 12:58:08 2021

@author: santi
"""
import sys
# khe = sys.argv[0] # Aquí está el nombre del archivo
texto = sys.argv[1]
# Es como el args de Java
repeticiones = int(sys.argv[2])
for r in range(repeticiones):
    #print(khe)
    print(texto)
# python lee_args.py "Hola" 5