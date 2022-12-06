import csv
from clases import Grafica
from teorema import Teorema

# Vamos a leer el archivo
import os, sys
os.chdir(r'C:/Users/santi/Documents/Coding/ESCUELA/Python/practica5 - AnalisisA/src')
f = open('entrada.txt', "r", newline='')
reader = csv.reader(f)
data = list(reader)

#Creamos la grafica con base en los datos
G = Grafica()
for i in data[0]:
    G.agrega(i) #Agregamos vertices de la primera linea
temp = 0
#Van los aristas
for i in data:
    if temp == 0: #Saltamos la primera linea
        temp += 1
        continue
    G.conecta(i[0], i[1], 0) # Le damos peso cero a nuestros aristas

H = set()
# Finalmente en esa lista guardaremos el conjunto
H = Teorema(G)
        
print("El conjunto independiente es:")

print("{", end="")
a = True
for i in H:
    if (a):
        print(i, end="")
        a = False
    else:  
        print(",", i, end="")
print("}")