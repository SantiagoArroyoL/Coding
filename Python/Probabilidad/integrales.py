from numpy import inf #infinito
from math  import e #Euler
from scipy.integrate import quad

def f(x,t):
    return x*2*t*(e**(-2*x*t))

# quad(f(x), a,b) - integra f(x) definida de "a" a "b". Parámetro opcional args
solution1 = quad(f,0,inf,args=(1)) #args hace t = 1
print(solution1)