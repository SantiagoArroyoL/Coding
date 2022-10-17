from clases import Vertice, Grafica, minHeap

""" Una implementacion de el algoritmo de Prim para busqueda de arboles de peso minimo usando heaps binarios (minHeap)

El algoritmo recibe una grafica y un vertice de donde partir

regresa: Un conjunto de aristas que conforman el arbol de peso minimo
"""
def Prim(G: Grafica, a: Vertice):
    T = set()
    Q = minHeap()
    a.set_marca(True)
    a.set_d(0)
    Q.inserta(a)
    while(not Q.vacia()):
        v = Q.eliminaMin()
        v.set_inT(True)
        L_v = v.vecinos
        for w in L_v:
            costo = G.get_aristas()[(v,w)]
            if not w.get_marca():
                w.set_marca(True)
                w.set_d(costo)
                w.set_inT(False)
                w.set_padre(v)
                Q.inserta(w)
            elif w.get_inT():
                pass
            elif costo < w.get_d():
                w.set_padre(v)
                w.set_d(costo)
                Q.reordena(w)
    T = set()     
    for v in G.get_vertices():
        if (v.get_inT() and v.get_padre()) and not v.prim:
            v.prim = True
            T.add((v.get_padre().get(), v.get() ,v.get_d()))
    return T
    
    
        
                
                
                
            
    
    

    
        
        
            