import random
from obj import Grafica, SAT_verificador

def alcanzabilidad(G: Grafica, s: int, t: int):
    H = set()
    x = G.vertice(s)
    z = G.vertice(t) 
    vertices = G.get_vertices()
    n = len(vertices)
    for _ in range(1,n):
        H.add(x)
        y = random.choice(vertices) # Fase adivinadora
        if (x, y) not in G.get_aristas(): # Fase verificadora
            continue
        if y == z:
            print("El camino correcto fue")
            for i in H:
                print(i)
            return True
        x = y
    print("El camino recorrido fue")
    for i in H:
        print(i, end=",")
    return False


def tres_SAT(input: str):
    S = SAT_verificador(input)
    clausulas = S.get_clausulas().values()
    literales = set()
    # vemos que literales se tienen para despues proponer
    for c in clausulas:
        for literal in c:
            if "NOT" in literal:
                literal = literal.replace("NOT", "")
            literales.add(literal)
    propuesta = ""
    x = True
    # Fase adivinadora
    for i in literales:
        if x:
            propuesta += "{id}={valor}".format(id=i, valor=random.randint(0,1))
            x = False
        else: 
            propuesta += ", {id}={valor}".format(id=i, valor=random.randint(0,1))
    #Fase verificadora
    return S.verifica(propuesta), propuesta