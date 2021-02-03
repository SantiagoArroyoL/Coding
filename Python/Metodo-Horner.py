# -*- coding: utf-8 -*-
"""
Created on Tue Feb  2 23:24:36 2021

@author: santi
"""

#Valor de x
valorX=8;
#Coeficientes del polinomio
coeficientes=[4,7,3,6,2];
resultado=0;
#Recorrer los coeficientes
for i in range(0,len(coeficientes)):
	#Multiplicar al valor parcial el valor de x más el coeficiente
	resultado= resultado * valorX + coeficientes[i]
print("Resultado:"+str(resultado))