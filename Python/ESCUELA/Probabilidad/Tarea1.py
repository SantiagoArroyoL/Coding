# -*- coding: utf-8 -*-
"""
Created on Tue Sep 29 00:18:03 2020

TAREA 1 - Probabilidad
@author: Santiago Arroyo
@author: David Lázaro
@author: Yonathan Berith Jaramillo Ramírez
"""

def sumaMala(x):
    i = 0
    suma = 0
    while i<=x:
        suma += i
        i += 1
    return suma
    
def suma(x):
    return int((x+1)*x/2)

#EJERCICIO 1 
print(sumaMala(100))

#EJERCICIO 2
n = int(input("Ingresa un número natural "))
print(suma(n))

#EJERCICIO 3
while True:
    try: 
        natural = int(input("Ingresa un número natural: "))
    except ValueError:
        print("Ingresaste un número inválido!")
    else:
        print(suma(natural))
        break