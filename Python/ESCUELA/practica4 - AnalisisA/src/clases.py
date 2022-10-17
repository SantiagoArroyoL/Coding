"""
Tenemos una cola de prioridades usando la implementacion
de un minHeap usando arreglos.

Muchos métodos se explican a si mismos, otros tendrán su documentacion

@author Santiago Arroyo
"""
import sys

#Queria que vertice fuera una clase anidada en Grafica pero decidi tambien usarla en minHeap
class Vertice:
        def __init__(self, elem):
            self.d = sys.maxsize #infinito
            self.inT = False
            self.elem = elem
            self.indice = 0 # indice para los minHeap
            self.vecinos = []
            self.visitado = False
            self.padre = None
            self.prim = False
            
        def set_padre(self, padre):
            self.padre = padre
            
        def get_padre(self):
            return self.padre
        
        def get_inT(self):
            return self.inT
        
        def set_inT(self, inT):
            self.inT = inT
        
        def get(self):
            return self.elem
        
        def get_indice(self):
            return self.indice
        
        def set_indice(self, indice):
            self.indice = indice
        
        def get_grado(self):
            return len(self.vecinos)
        
        def set_marca(self, visitado):
            self.visitado = visitado
        
        def set_d(self, d):
            self.d = d
            
        def get_d(self):
            return self.d
        
        def get_marca(self):
            return self.visitado
        
        def __str__(self):
            return str(self.elem)
"""Clase Monticulo Minimo jaja

La implementacion de un minHeap usando arreglos como representacion
El orden de los elementos se rige por su elemento d (distancia actual), propiedad de cada vertice 

Esta estructura de datos esta bien formada y a prueba de tontos, cada que se inserta o elimina un elemento reordenamos y verificamos
"""
class minHeap:
    
    #Creamos un arreglo nuevo con tamanio arbitrario
    def __init__(self):
        self.H = [None]*50
        self.size = 0
        
    #Creamos un heap a aprtir de una instancia iterable
    def creaHeap(self, iterable):
        n = len(iterable)
        self.H = [None]*n
        self.size = n
        c = 0
        for elem in iterable:
            self.H[c] = elem;
            c += 1
        limite = (n//2)-1;
        for i in range(limite, -1, -1):
            self.abajo(self.H[i]);
    
    def padre(self, i):
        return (i - 1) // 2
    
    def izq(self, i):
        return 2 * i + 1
    
    def der(self, i):
        return 2 * i + 2
        
    """
        movemos "hacia arriba" un elemento v en la cola de prioridades
        heapifyUp
    """    
    def arriba(self, v):
        if (not v):
            return
        index = v.get_indice()
        padre = self.padre(v.get_indice())
        if(index <= 0):
            return
        if (not self.H[padre]):
            return
        if (self.H[padre].get_d() < self.H[index].get_d()):
            return
        self.intercambia(index,padre)
        self.arriba(self.H[padre])
      
    """
        movemos "hacia abajo" un elemento v en la cola de prioridades
        heapifyDown
    """          
    def abajo(self, v):
        if (not v):
            return
        i = v.get_indice()
        izq = self.izq(i)
        der = self.der(i)
        min = i
        if (self.size <= i):
            return
        if izq < self.size and self.H[izq].get_d() < self.H[i].get_d():
            min = izq
        if der < self.size and self.H[der].get_d()  < self.H[min].get_d():
            min = der
        if (min == i):
            return
        self.intercambia(i,min);
        self.abajo(self.H[min]);
            
    def inserta(self, v):
        if len(self.H) == self.size:
            temp = self.H;
            self.H = [None]*(self.size*2)
            for i in range(0, self.size):
                self.H[i] = temp[i];
        self.H[self.size] = v;
        v.set_indice(self.size);
        self.size += 1
        self.arriba(v);
    
    #Eliminamos el elemento con d mas chico en el heap    
    def eliminaMin(self):
        temp = self.H[0]
        self.elimina(temp)
        return temp
    
    def elimina(self, elem):
        if not elem:
            return
        i = elem.get_indice()
        if (i < 0 or i >= self.size):
            return
        self.intercambia(i,self.size-1)
        self.H[self.size-1] = None
        self.size -= 1
        self.arriba(self.H[i])
        self.abajo(self.H[i])
        elem.set_indice(-1)
        return elem
        
    def reordena(self, v):
        i = v.get_indice()
        if (i < 0 or i >= self.size):
            return
        self.arriba(v);
        self.abajo(v);
    
    def intercambia(self, x, y):  
        self.H[x].set_indice(y);
        self.H[y].set_indice(x);
        temp = self.H[x];
        self.H[x] = self.H[y];
        self.H[y] = temp;
        
    def vacia(self):
        return self.size <= 0
    
    def Print(self):
        for i in self.H:
            print(i)
        


"""
Una simple implementacion de una grafica.
NO VERIFICA LOS METODOS

Es decir, como estructura de datos tiene varias fallas ya que asume que el usuario de esta hara las cosas bien
NO se verifica si el vertice agregado es repetido o no, no se verifica que el arista agregado exista o no
"""
class Grafica:
        
    # Variables de clase    
    __vertices = []
    __aristas = dict()
    
    def get_primero(self) -> Vertice:
        return self.__vertices[0]    
    
    def get_elementos(self):
        return len(self.__vertices)
    
    def get_vertices(self):
        return self.__vertices
    
    def get_aristas(self):
        return self.__aristas
    
    def agrega(self, elem):
        self.__vertices.append(Vertice(elem))
        
    # Creamos los aristas, creamos el arista (v,u) y (u,v)
    # Son el mismo arista pero es así para poder implementar una digrafica en un futuro
    def conecta(self, a, b, peso):
        v = self.vertice(a)
        u = self.vertice(b)
        self.__aristas[(v,u)] = peso
        self.__aristas[(u,v)] = peso
        v.vecinos.append(u)
        u.vecinos.append(v)
        
    def contiene(self, elem):
        for v in self.__vertices:
            if v.get() == elem:
                return True
        return False
    
    # Buscamos un vertice dentro de la grafica
    def vertice(self, elem):
        for v in self.__vertices:
            if v.get() == elem:
                return v
        return None
    
    def Print(self):
        print("VERTICES:")
        for i in self.__vertices:
            print(i)
        print("ARISTAS:")
        for (v,w) in self.__aristas:
            a = str(v), str(w)
            print(a, self.__aristas[(v,w)])