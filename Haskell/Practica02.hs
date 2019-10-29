--Practica2
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

--Lista por comprension
tamanioLista:: [a]->Int
tamanioLista [] = 0
tamanioLista (x:xs) = 1 + tamanioLista xs

--Máximo de una Lista
maximo:: Ord a => [a]-> a
maximo (y:ys) = maximoAux ys y
maximo[x] = x
maximo (x:xs) = if x > maximo xs
	            then x
					else maximo xs
--Funcion Auxiliar para hacer más eficiente el proceso de comparación
maximoAux:: Ord a => [a] -> a ->a
maximoAux [ ] x = x
maximoAux (y:ys) x = if x <y
	                  then maximoAux ys y
							else maximoAux ys x

--Lugar del elemento
indiceDe:: Int-> [a] -> a
indiceDe 0 (x:xs) = x
indiceDe n (x:xs)= if n < 0 || n > tamanioLista (x:xs)
	              then error "No estes molestando"
					  else indiceDe (n-1) xs
indiceDe 0 [] = error "Mensaje de error"
