# -*- coding: utf-8 -*-
"""
Created on Mon May 23 22:24:21 2022

@author: Santiago Arroyo Lozano
"""

import sys
from random import randint 
import matplotlib.pyplot as plt

# PROBLEMA ADOQUINAMIENTO
k = int(sys.argv[1])
tamano = 2**k
cnt = 0
arr = [[0 for i in range(tamano)] for j in range(tamano)]
 
def coloca(x1, y1, x2, y2, x3, y3):
    global cnt
    cnt += 1
    arr[x1][y1] = cnt;
    arr[x2][y2] = cnt;
    arr[x3][y3] = cnt;
     
def adoquina(n, x, y):
    global cnt
    r = 0
    c = 0
    if (n == 2):
        cnt += 1
        for i in range(n):
            for j in range(n):
                if(arr[x + i][y + j] == 0):
                    arr[x + i][y + j] = cnt
        return 0;   
    for i in range(x, x + n):
        for j in range(y, y + n):
            if (arr[i][j] != 0):
                r = i
                c = j 
    if (r < x + n / 2 and c < y + n / 2):
        coloca(x + int(n / 2), y + int(n / 2) - 1, x + int(n / 2), y + int(n / 2), x + int(n / 2) - 1, y + int(n / 2))
     
    elif(r >= x + int(n / 2) and c < y + int(n / 2)):
        coloca(x + int(n / 2) - 1, y + int(n / 2), x + int(n / 2), y + int(n / 2), x + int(n / 2) - 1, y + int(n / 2) - 1)
     
    elif(r < x + int(n / 2) and c >= y + int(n / 2)):
        coloca(x + int(n / 2), y + int(n / 2) - 1, x + int(n / 2), y + int(n / 2), x + int(n / 2) - 1, y + int(n / 2) - 1)
     
    elif(r >= x + int(n / 2) and c >= y + int(n / 2)):
        coloca(x + int(n / 2) - 1, y + int(n / 2), x + int(n / 2), y + int(n / 2) - 1, x + int(n / 2) - 1, y + int(n / 2) - 1)
     
    adoquina(int(n / 2), x, y + int(n / 2));
    adoquina(int(n / 2), x, y);
    adoquina(int(n / 2), x + int(n / 2), y);
    adoquina(int(n / 2), x + int(n / 2), y + int(n / 2));
     
    return 0
 
# AGREGAMOS ADOQUIN INVALIDO Y EJECUTAMOS

a = randint(0, tamano-1)
b = randint(0, tamano-1)
arr[a][b] = -1
adoquina(tamano, 0, 0)

for i in range(tamano):
    for j in range(tamano):
        print(arr[i][j], end=" ")
    print()

img = plt.matshow(arr, extent = [0, tamano, 0 , tamano])
plt.show(img)