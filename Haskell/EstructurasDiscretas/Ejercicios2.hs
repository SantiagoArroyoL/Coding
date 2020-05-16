--Fecha: 11 oct 2019
data ArbolBinario a = Hoja | Nodo a (ArbolBinario a ) (ArbolBinario a )

nHojas:: ArbolBinario a -> Int
nHojas Hoja = 1
nHojas (Nodo x xs ys) = nHojas xs + nHojas ys

nElementos:: ArbolBinario a -> Int
nElementos Hoja = 0
nElementos (Nodo x xs ys) = 1 + nElementos xs + nElementos ys

--Orden del ArbolBinario

preOrden:: ArbolBinario a -> [a]
preOrden Hoja = []
preOrden (Nodo x xs ys) = (x:(preOrden xs ++ preOrden ys))
