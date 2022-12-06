import random
from obj import Grafica, SAT_verificador
from non_det_algos import alcanzabilidad, tres_SAT

#-------------------------------------> ALCANZABILIDAD <--------------------------------------------
#-------------------------------------> ALCANZABILIDAD <--------------------------------------------
#-------------------------------------> ALCANZABILIDAD <--------------------------------------------
#-------------------------------------> ALCANZABILIDAD <--------------------------------------------
# Creamos una lista aleatoria de vertices. La grafica puede tener a lo mas 25 vertices
n = random.randint(10,25)  # Siempre habra al menos 10 vertices
n_aristas = random.randint(1,20) #Maximo 20 aristas, minimo 1
vertices = []
for i in range(1,n):
    vertices.append(i)
aristas = tuple((random.choice(vertices), random.choice(vertices)) for _ in range(n_aristas))

#Creamos la grafica con base en los datos
G = Grafica()
for i in vertices:
    G.agrega(i) #Agregamos vertices 
temp = 0
#Van los aristas
for i in aristas:
    G.conecta(i[0], i[1], 0) # Le damos peso cero a nuestros aristas

#NON DET
G.Print()
if alcanzabilidad(G,1,4):
    print("\nExiste el camino entre los vertices!!")
else:
    print("\nLamentablemente no es un camino valido :(")
    
print("*****************************************************************")
print("*****************************************************************")
print("*****************************************************************")
#-------------------------------------> 3-SAT <--------------------------------------------
#-------------------------------------> 3-SAT <--------------------------------------------
#-------------------------------------> 3-SAT <--------------------------------------------
#-------------------------------------> 3-SAT <--------------------------------------------
print("*****************************************************************")
print("*****************************************************************")
print("*****************************************************************")


print("3SAT")
# Construimos de forma aleatoria un problema 3SAT
literales = 10
clausulas = 5
c = ""
txt = ""
for i in range(clausulas):
    c = "(x{0} OR x{1} OR x{2})".format(random.randint(1,literales), random.randint(1,literales), random.randint(1,literales))
    if i != clausulas-1:
        txt += c+" AND "
    else:
        txt += c
b,x = tres_SAT(txt)
print("La formula es", txt)
print("Se propuso", x)
if (b):
    print("Es una solucion aceptada!")
else:
    print("Lamentablemente no es solucion :(")