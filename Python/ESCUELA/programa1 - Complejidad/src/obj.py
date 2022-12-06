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
"""
Una simple implementacion de una grafica dirigida.
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
        
    # Creamos el arista (v,u)
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
            print(i, end=",")
        print("\nARISTAS:")
        for (v,w) in self.__aristas:
            a = str(v), str(w)
            print(a, self.__aristas[(v,w)])
 
"""
   Objeto que verifica si dado un ejemplar de SAT y una configuracion esta es valida      
"""            
class SAT_verificador:
    
    # Variables de clase    
    __clausulas = dict()
    __solucion = dict()
    literales = 3 #Esto para que el codigo funcione para otros casos de SAT
    
    # Recibimos la cadena que representa SAT
    def __init__(self, input:str):
        input = input.replace(" ", "")
        input = input.replace("(", "")
        input = input.replace(")", "")
        clausulas = input.split("AND")
        i = 0
        for c in clausulas:
            if (c.count("OR") != self.literales-1): #si tiene el numero correcto de OR's entonces es un SAT bien formado
                raise Exception("La clausula no esta bien formada!\nPor favor revisa la entrada")
            self.__clausulas[i] = c.split("OR")
            i += 1
    
    """
        Metodo que verifica una solucion del SAT 
    """
    def verifica(self, input:str) -> bool:
        input = input.replace(" ", "")
        input = input.replace("(", "")
        input = input.replace(")", "")
        temp = input.split(",")
        for i in temp:
            x = i.split("=")
            if x[1] == "1":
                self.__solucion[x[0]] = True
            else: 
                self.__solucion[x[0]] = False
        # Ahora si, revisemos si cumple el SAT
        validezAND = True
        for c in self.__clausulas.values():
            validezC = False
            for literal in c:
                if "NOT" in literal:
                    validezC = validezC or not self.__solucion[literal.replace("NOT", "")]
                else:
                    validezC = validezC or self.__solucion[literal]
                # Si el OR es valido on tiene caso seguir recorriendo
                if validezC:
                    break
            validezAND = validezAND and validezC
            # Si el AND no es valido on tiene caso seguir recorriendo
            if(not validezAND):
                break
        return validezAND
    
    def get_clausulas(self):
        return self.__clausulas
        
        
        
    