def suma(x,y):
    try:
        r = x+y
    except TypeError:
        print("Error: Tipo de dato no válido")
    else:
        return r
    
    return r

def resta(x,y):
    try:
        r = x-y
    except TypeError:
        print("Error: Tipo de dato no válido")
    else:
        return r

def producto(x,y):
    try:
        r = x*y
    except TypeError:
        print("Error: Tipo de dato no válido")
    else:
        return r

def division(x,y):
    try:
        r = x/y
    except TypeError:
        print("Error: Tipo de dato no válido")
    except ZeroDivisionError:
        print("Error: No es posible dividir entre cero")
    else:
        return r