--Practica02
--Programador: Arroyo Lozano Santiago

--Función conjuncion
conjuncion:: Bool->Bool->Bool
conjuncion True True = True
conjuncion True False = False
conjuncion False True = False
conjuncion False False = False

--Función disyuncion
disyuncion:: Bool->Bool->Bool
disyuncion True True = True
disyuncion True False = True
disyuncion False True = True
disyuncion False False = False

--Funcion implicacion
implicacion:: Bool->Bool->Bool
implicacion True True = True
implicacion True False = False
implicacion False True = True
implicacion False False = True

--Funcion Bicondicional
dobleImplica:: Bool->Bool->Bool
dobleImplica True True = True
dobleImplica True False = False
dobleImplica False True = False
dobleImplica False False = True

--Longitud
longitud:: (Num b) => [a] -> b
longitud [] = 0
longitud (x:xs) = 1 + longitud xs

--Suma de números
sumaNumeros:: (Num a) => [a] -> a
sumaNumeros [] = 0
sumaNumeros (x:xs) = x + sumaNumeros xs

--Máximo de una Lista
maximo:: Ord a => [a]-> a
maximo[x] = x
maximo[] = error "La lista está vacía"
maximo (x:xs) = if x > maximo xs
	then x
	else maximo xs

--Funcion auxilliar de tamaño de lista
tamanioLista:: [a]->Int
tamanioLista [] = 0
tamanioLista (x:xs) = 1 + tamanioLista xs
--Lugar del elemento
indiceDe:: Int-> [a] -> a
indiceDe 0 (x:xs) = x
indiceDe n (x:xs)= if n < 0 || n > tamanioLista (x:xs)
	then error "El elemento que buscas no esta en la lista"
	else indiceDe (n-1) xs

--Función insertar
insertarElemento:: a -> [a] -> Bool -> [a]
insertarElemento x xs True = (x:xs)
insertarElemento x xs False = (xs)++[x]

--reversa
reversa:: [a] -> [a]
reversa [] = []
reversa (x:xs) = reversa xs ++ [x]

--Palindromo
esPalindromo:: Eq a => [a] -> Bool
esPalindromo xs = reversa xs == xs

--Funcion auxiliar busquedaLista
busquedaLista:: Eq a => [a] -> a -> Bool
busquedaLista [] e = False
busquedaLista (x:xs) e = if x == e
	then True
	else busquedaLista xs e
--Conjunto
aConjunto:: Eq a => [a] -> [a]
aConjunto [] = []
aConjunto (x:xs) = if busquedaLista xs x
   then aConjunto xs
	else [x] ++ aConjunto xs

--Union
union:: Eq a => [a] -> [a] -> [a]
union xs ys = aConjunto(xs ++ ys)

--Interseccion
interseccion:: Eq a => [a] -> [a] -> [a]
interseccion [] [] = []
interseccion xs [] = []
interseccion [] xs = []
interseccion (x:xs) (y:ys) = if busquedaLista (y:ys) x
	then aConjunto ([x] ++ interseccion xs (y:ys))
	else interseccion xs (y:ys)

--Producto Cruz
productoCruz :: [a] -> [b] -> [(a, b)]
productoCruz xs ys = [(x, y) | x <- xs, y <- ys]

--Diferencia Simetrica
--Función auxiliar diferencia
diferencia:: Eq a => [a] -> [a] -> [a]
diferencia xs ys = aConjunto (xs++ys)
diferenciaSimetrica :: Eq a => [a] -> [a] -> [a]
diferenciaSimetrica xs ys = diferencia (union xs ys) (interseccion xs ys)

--Función Auxilir divisibles
divisible::Int->Int->Bool
divisible x y = (mod x y) == 0
--Divisores
divisores::Int->[Int]
divisores x = [y | y <-[1..x],divisible x y]

--ConjuntoPotencia
conjuntoPotencia:: Eq a => [a] -> [[a]]
conjuntoPotencia [] = [[]]
conjuntoPotencia (x:xs) = agregar x (conjuntoPotencia xs) ++ (conjuntoPotencia xs)
{--FuncionAuxiliar agregar
No necesita ser declarada
agregar:: Eq a => a -> [a] -> [a]--}
agregar x [] = []
agregar x (y:ys) = (x:y) : agregar x ys
