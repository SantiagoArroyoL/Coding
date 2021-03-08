# -*- coding: utf-8 -*-
"""
Created on Wed Feb  3 13:56:23 2021

@author: santi
"""
import sys
if len(sys.argv) != 3:
    sys.exit("No has escrito los parámetros necesarios\nEjemplo: tabla.py [1-9] [1-9]")  
    
x = int(sys.argv[1])
y = int(sys.argv[2])

if (x < 1 or x > 9) or (y < 1 or y > 9):
    sys.exit("Debes escribir números enteros del 1 al 9")  

for i in range(x):
    print("")
    for j in range(y):
        print(" * ", end='')
