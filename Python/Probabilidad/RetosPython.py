# -*- coding: utf-8 -*-
"""
Created on Fri Oct  2 11:27:53 2020

Retos Python
@author: Santiago Arroyo
"""

import sys 
import random

input("Presiona enter para saber tu fortuna")
#Galleta de la Fortuna
fortunas = []
fortunas.append("Hoy tus alumnos te harán muchas preguntas")
fortunas.append("Hoy le darán un aumento a los ayudantes de la Facultad")
fortunas.append("Hoy Julio conseguirá un nuevo ayudante")
fortunas.append("Hoy tu crush te mandará un mensaje")
fortunas.append("Hoy excentarás a todos tus alumnos")
x = random.randint(0, 4)
print("****************************************")
print("La fortuna de hoy es: \n ", fortunas[x])
print("****************************************")

input("Presiona enter para lanzar una moneda 100 veces")
# LANZAMIENTO DE MONEDA
cara = 0
cruz = 0
for amount in range(100):
    flip = random.randint(0, 1)
    if (flip == 0):
        cara += 1
    else:
        cruz += 1
print("Veamos los resultados de lanzar una moneda 100 veces:")
print("Resultó Cara:", cara, "veces\nResultó Cruz:",cruz,"veces")

input("Presiona enter para jugar a 'Guess my Number'")
# GUESS MY NUMBER
print("\tBienvenido a 'Guess My Number'!")
print("\nEstoy pensando en un número del 1 al 100")
print("Intenta adivinarlo en la menor cantidad de intentos posibles")

#Inicializamos el número aleatorio
el_numero = random.randint(1, 100)

"""
La función randInt(a,b), donde a y b son números enteros,
elige un úmero entero (pseudo) aleatorio entre a,a+1,a+2,...,b
"""

guess = int(input("Intenta adivinar: "))
intentos = 0

#Entramos en el loop de la adivinanza
while guess != el_numero:
    intentos = intentos+1 if intentos+1 < 10 else sys.exit('Has sobrepasado el máximo de intentos permitidos')
    if guess > el_numero:
        print("Intenta con un número más bajo...")
    else:
        print("Intenta con un número más alto...")
    guess = int(input("Intenta adivinar: "))
print("¡Adivinaste! El número era: ", el_numero)
print("Sólo te tomó", intentos, "intentos")

input("\nPresiona enter para terminar el programa")

