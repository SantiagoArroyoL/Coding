# -*- coding: utf-8 -*-
"""
Created on Fri Oct  2 11:43:19 2020

Guess My Number

La computadora selecciona un número aleatorio entre 1 y 100.
EL jugador intenta adivinar el número y la computadora le dapistas al jugador
Diciendo si este se pasó, si va muy abajo o si adivinó correctamente

Libro: Python programming for th absolute beginner
Author: Michael Dawson

@author: Santiago Arroyo
"""

import random

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
intentos = 1

#Entramos en el loop de la adivinanza
while guess != el_numero:
    if guess > el_numero:
        print("Intenta con un número más bajo...")
    else:
        print("Intenta con un número más alto...")
    guess = int(input("Intenta adivinar: "))
    intentos += 1
print("¡Adivinaste! El número era: ", el_numero)
print("Sólo te tomó", intentos, "intentos")

input("\nPresiona enter para terminar el programa")