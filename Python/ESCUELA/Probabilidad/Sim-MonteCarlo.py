# -*- coding: utf-8 -*-
"""
Created on Sun Jan 31 01:00:38 2021

@author: santi
"""
import random

def random_walk(n):
    """Return coordinates after 'n' block random walk"""
    x = 0
    y = 0
    for i in range(n):
        step = random.choice(['N','S','E','W'])
        if step == 'N':
            y = y+1
        elif step == 'S':
            y = y-1
        elif step == 'E':
            x = x+1
        else:
            x = x-1
    return (x,y)

"""for i in range(25):
        walk = random_walk(10)
        print(walk, "Distance from home = ", abs(walk[0]) + abs(walk[1]))"""

# Mejorando esa función
def caminata_aleatoria(n):
    #Regresa las coordenadas después de 'n' bloques caminados al azar
    x,y = 0,0
    for i in range(n):
        (dx, dy) = random.choice([(0,1),(0,-1),(1,0),(-1,0)])
        x += dx
        y += dy
    return (x, y)


# SIMULACION MONTECARLO
numero_de_caminatas = 100000

for longitud_caminata in range(1, 31):
    transporte = 1 #Número de caminatas donde quedamos 4 bloques o menos cerca de casa y por tanto no debemos usar transporte
    for i in range(numero_de_caminatas):
        (x,y) = caminata_aleatoria(longitud_caminata)
        distancia = abs(x) + abs(y)
        if distancia <= 4:
            transporte += 1