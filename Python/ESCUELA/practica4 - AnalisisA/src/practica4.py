import csv
from prim import Prim
from clases import Grafica

# Vamos a leer el archivo
f = open("entrada.txt", "r", newline='')
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
    G.conecta(i[0], i[1], i[2])

listaFinal = []
# Finalmente en esa lista guardaremos cada conjunto de aristas
#  que conformen el arbol de peso minimo de cada componente conexa
#  Gracias a la magia de la POO, cada que se haga Prim() se actualizan todos los vertices
#  Y asi el bucle for solo se ejecutará tantas veces como haya componentes conexas en la grafica
for v in G.get_vertices():
    if not v.prim:
        listaFinal.append(Prim(G, v))
        
print("El bosque generador de peso minimo es:\n", listaFinal)

for i in range(len(listaFinal)):
    print("COMPONENTE CONEXA", i+1)
    for j in listaFinal[i]:
        print("Arista:", j[0], j[1], "de peso", j[2])
