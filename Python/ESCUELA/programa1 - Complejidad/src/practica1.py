import random
from obj import Grafica
from non_det_algos import alcanzabilidad

#-------------------------------------> ALCANZABILIDAD <--------------------------------------------
# Creamos una lista aleatoria de vertices. La grafica puede tener a lo mas 25 vertices
n = random.randint(10,25)  # Siempre habra al menos 10 vertices
n_aristas = random.randint(0,20) #Siempre habra a lo mas 20 aristas
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
print(alcanzabilidad(G,1,4))


#-------------------------------------> 3-SAT <--------------------------------------------

