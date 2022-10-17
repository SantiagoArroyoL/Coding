import random
from obj import Grafica, Vertice

def alcanzabilidad(G: Grafica, s: int, t: int):
    H = set()
    x = G.vertice(s)
    z = G.vertice(t) 
    vertices = G.get_vertices()
    n = len(vertices)
    for _ in range(1,n):
        H.add(x)
        y = random.choice(vertices)
        if (x, y) not in G.get_aristas():
            continue
        if y == z:
            print("El camino correcto fue")
            for i in H:
                print(i)
            return True
        x = y
    print("El camino recorrido fue")
    for i in H:
        print(i)
    return False
