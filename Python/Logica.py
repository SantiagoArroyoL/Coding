#!/usr/bin/env python
# coding: utf-8
''' 
@author Santiago Arroyo Lozano
Programa que imprime en LaTex las resoluciones de un sistema lógico
'''

#Definimos un objeto que simula la variable proposicional
class Proposicion:
  #Constructor
  def __init__(self, antes, cadena):
    self.antes = antes
    self.cadena = cadena
  #Métodos de la clase
  def negacion(self):
        return Proposicion(not self.antes, self.cadena)
  def __eq__(self, obj):
        return isinstance(obj, Proposicion) and self.cadena == obj.cadena and self.antes == obj.antes
  def __str__(self):
        if(self.antes):
            return self.cadena
        else: 
            return "\\neg "+self.cadena
#CIERRE DE LA CLASE

#Definimos nuestras variables (instancias de proposicion)
s = Proposicion(True,"s")
ns = s.negacion()
p = Proposicion(True,"p")
np = p.negacion()
m = Proposicion(True,"m")
nm = m.negacion()
l = Proposicion(True,"l")
nl = l.negacion()
n = Proposicion(True,"n")
nn = n.negacion()
q = Proposicion(True,"q")
nq = q.negacion()
t = Proposicion(True,"t")
nt = t.negacion()

# Dado que ya todos están en FNC no necesitamos definir otros operadores.
# Sabemos que si hay una coma es un \lor (Conjunción,\vee)
hipotesis=[
    [s, np, m, l], #1
    [s, np, nq, nn], #2
    [np, q],#3
    [np, l], #4
    [nq, nl, p], #5
    [nn,nt], #6
    [nn,q], #7
    [nn,l], #8
    [ns,nt], #9
    [ns,q], #10
    [ns,l], #11
    [m,nt], #12
    [m,q], #13
    [m,l], #14
    [ns], #15
    [nm], #16
    [n] #17
]
# Esta es una mausque herramienta que nos ayudará más tarde
iteraciones = []

# Quita un elemento de la lista
def quitar(p, arreglo):
    resultado=[];
    for i in arreglo:
        if not p==i: 
            resultado= resultado+[i]
    return resultado

# Este método es el que hace la resolución como tal
# Nada eficiente por cierto. O(n^2) creo
# Recibe dos listas. Revisando cada elemento de la primera revisa a su vez que
# NO esté su negación. Si lo está la quita (Revisa n veces n elementos)
def resolucionBinaria(c1, c2,iteracion):
    for d1 in iteracion[c1]: 
        if d1.negacion() in iteracion[c2]: 
                return quitar(d1.negacion(),quitar(d1, iteracion[c1]+iteracion[c2]))

#imprimimos la resolución en LaTex
def resolucionImprimible(x,y,iteracion):
    print("\item $", end='')
    if(resolucionBinaria(x,y,iteracion)!= None):
        temp = 0
        largo = len(resolucionBinaria(x,y,iteracion))
        for i in resolucionBinaria(x,y,iteracion): 
            temp += 1
            if (temp == largo):
                print(i, end='')
            else:
                print(i, end='\lor ')
        print("$ (Resolución de "+str(x+1)+" y "+str(y+1)+")")
        return resolucionBinaria(x,y,iteracion);
    else: 
        return []

# HAGAMOSLO!
x = hipotesis
for i in range(0,len(x)):
    for j in range(i+1, len(x)):
         if(resolucionBinaria(i,j,hipotesis) != None):
            iteraciones = iteraciones + [resolucionImprimible(i,j,hipotesis)]

# SEGUNDA ITERACION
x = iteraciones
iteraciones_dos= []
for i in range(0,len(x)):
    for j in range(i+1, len(x)):
          if(resolucionBinaria(i,j,iteraciones)!= None):
            iteraciones_dos = iteraciones_dos + [resolucionImprimible(i,j,iteraciones)]

# # TERCERA ITERACION
# x = iteraciones_dos
# iteraciones_tres = []
# for i in range(0,len(x)):
#     for j in range(i+1, len(x)):
#           if(resolucionBinaria(i,j,iteraciones_dos)!= None):
#             iteraciones_tres = iteraciones_tres + [resolucionImprimible(i,j,iteraciones_dos)]

