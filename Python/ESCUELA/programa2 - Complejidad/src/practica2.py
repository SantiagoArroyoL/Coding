"""
   @author Santiago Arroyo Lozano
   @date  30/11/2022
   
   Programa 2 - Complejidad Computacional 2023-1
   Se implementa un algoritmo de aproximacion para subset sum
"""
def Trim(L, d):
    m = len(L)
    L_p = [L[0]]
    last = L[0]
    for i in range(1,m):
        if L[i] > (last * (1+d)):
            L_p.append(L[i])
            last = L[i]
    return L_p


def Merge_Lists(L_1,L_2):
    i = j = 0
    n1 = len(L_1)
    n2 = len(L_2)
    L = []
    while i < n1 and j < n2:
        if L_1[i] <= L_2[j]:
            L.append(L_1[i])
            i += 1
        else:
            L.append(L_2[j])
            j += 1
    L = L + L_1[i:] + L_2[j:]
    return L

def Approx_Subset_Sum(S,t,e):
    n = len(S)
    L = [[0]] * n
    for i in range(0,n):
        L[i] = Merge_Lists(L[i-1],[l+S[i] for l in L[i-1]])
        L[i] = Trim(L[i], e/(2*n))
        L[i] = [x for x in L[i] if x <= t]
    z = max(L[n-1])
    return z

#[--------------------------------------> MAIN <--------------------------------------]
#[--------------------------------------> MAIN <--------------------------------------]
#[--------------------------------------> MAIN <--------------------------------------]
S = [1,348,349,350,1,2,3,4,2,6,5,7,1000,123]
t = 665
e = 0.40
z = Approx_Subset_Sum(S,t,e)

print("El ejemplar de entrada fue un conjunto S:", S)
print("Buscando un t =", t)
print("Con un epsilon =", e)
print("Dándonos de resultado un z =",z,"que es una respuesta aceptada en el rango de epsilon%")