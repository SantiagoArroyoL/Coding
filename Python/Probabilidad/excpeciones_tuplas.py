# -*- coding: utf-8 -*-
"""
Editor de Spyder

Excepciones y manejo de tuplas con coma
@author Santiago Arroyo
"""
a = 5
b = 10
print(a,b)
a,b = b,a #Intercambiamos valores
print(a,b)
x,y=24,56 
#La coma basicamente genera una tupla, esta despues es desempaquetada a como se necesite

#Bucles y excpeciones

while True:
    try: 
        entero = int(input("Ingresa un número entero: "))
    except ValueError:
        print("Ingresaste un número inválido!")
    else:
        print("Elegiste el número: ", entero)
        break

""" En escecia es lo mismo que:
while true {
    try {} catch (ValueError){}             
   }    
"""
x0 = 0
x1 = 1

while x1<20:
    print(x1)
    x0,x1 = x1,x0+x1
