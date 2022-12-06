from clases import Vertice, Grafica

def independiente(H: set):
    for v in H:
        for w in v.vecinos:
            if (w in H):
                return False
    return True
           
def Teorema(G: Grafica):
    v = G.get_primero()
    H = set()
    H.add(v)  
    for v in G.get_vertices():
        H.add(v)
        if (independiente(H)):
            continue
        else:
            H.remove(v)
            for w in H:
                if w in v.vecinos:
                    H.add(w)
    return H
        
    