# -*- coding: utf-8 -*-
"""
Created on Fri Oct  2 11:36:50 2020

Simulador de conversación infantil
Demostramos un uso de la variable centinela y el bucle while

Libro: Python programming for the absolute beginner
Autor: Michael Dawson

@author: Santiago Arroyo
"""

print("\t Bienvenido al 'Simulador de Conversación Infantil'\n")
print("Este progrma simula una conversación cno un niño de tres años")
print("Intenta detener esta locura")

response = "" # Valor centinela
while response != "Because.":
    response = input("Why?\n")
else:
    print("Oh, okay.")

input("Presiona enter para terminar")
