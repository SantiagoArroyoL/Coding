tamanio:: [a]->Int
tamanio [] = 0
tamanio (x:xs) = 1 + tamanio xs

--Rotar Lista
rotar:: Int -> [a] -> [a]
rotar 0 xs = xs
rotar i (x:xs) = rotar (i-1) (xs++[x])

--Mezcla
mezcla:: Ord a => [a] -> [a] -> [a]
mezcla xs [] = xs
mezcla [] xs = xs
mezcla (x:xs) (y:ys) = if (x < y)
	                    then
								  (x:mezcla xs (y:ys))
								else (y:mezcla (x:xs)ys)
--División
divide:: [a] -> [a] -> Int -> ([a],[a])
divide xs ys 0 = (xs,ys)
divide xs (y:ys) n = divide (y:xs) ys (n-1)
--Función Auxiliar
coordenada:: ([a],[a]) -> Bool -> [a]
coordenada (x,y) True = x
coordenada (x,y) False = y

mergeSort::Ord a => [a] -> [a]
mergeSort [] = []
mergeSort xs = mezcla (mergeSort(coordenada(divide []xs (tamanio xs) /2)True))
               (mergeSort(coordenada(divide [] xs (tamanio xs) /2)False))

--Factorial
factorial:: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n-1)

--emparejaListas
emparejaListas :: [a] -> [a] -> [(a,a)]
emparejaListas [] _ = []
emparejaListas _ [] = []
emparejaListas (x:xs) (y:ys) = (x,y) : (emparejaListas xs ys)
