# -*- coding: utf-8 -*-
"""
Created on Thu Nov 23 17:39:06 2023

@author: santi
"""

def calcular_epsilon_de_maquina():
    epsilon = 1.0
    while (1.0 + epsilon) > 1.0:
        epsilon /= 2.0
    return epsilon * 2.0

# Usar la función para calcular el épsilon de la máquina
mu = calcular_epsilon_de_maquina()
print("El épsilon de la máquina es:", mu)
