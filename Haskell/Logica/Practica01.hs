{-- Práctica01 - Lógica Computacional
Equipo:
 EQUIPO ALFA DINAMITA BUENA ONDA ESCUADRÓN LOBO
Integreantes:
 Arroyo Lozano Santiago - 317150700
 Arévalo Gaytan Rodrigo - 317285880
--}
module Practica01 where

--primitivo. Función que recibe un entero y devuelve su primitivo.
primitivo :: Int -> Int
primitivo n = if n < 10
	then n
	else primitivo(producto(digitos n))
-- digitos. función que me da una lista de los digitos de un número en orden
digitos :: Int -> [Int]
digitos n
 | n<10 = [n]
 |otherwise = reverse((mod n 10) : reverse(digitos (div n 10)))
--producto. función que me regresa el producto de números en una lista
producto :: [Int] -> Int
producto [] = 1
producto (x:xs) = x * (producto xs)

--area. Función que recibe tres puntos y devuelve el área del
--      triángulo formado.
area :: (Double, Double) -> (Double, Double) -> (Double, Double) -> Double
area (x1,y1) (x2,y2) (x3,y3) = if total < 0
	then total*(-1)
	else total
	where total = (((x1*y2)+(x2*y3)+(x3*y1))-((x1*y3)+(x3*y2)+(x2*y1)))*0.5

--heterograma. Función que recibe una cadena y lo convierte en un
--             heterograma.
heterograma :: String -> String
heterograma [] = []
heterograma (x:xs) = if notElem x xs
	then [x]++ heterograma xs
	else heterograma xs

--bolsa. Función que recibe una cadena y devuelve una lista de tuplas
--       con el número de ocurrencias de cada letra de la palabra.
-- bolsa :: Eq a => String -> [(a, b)] //Se preguntó por correo de esta firma y notamos que era incorrecta
bolsa :: String -> [(Char, Int)]
bolsa [] = []
bolsa (x:xs) = if elem x xs
	then [(x, cuenta x (x:xs))] ++ bolsa (diferencia xs [x])
	else [(x, 1)] ++ bolsa xs
-- Cuenta cuántas veces se repite un caracter en la lista recibida
cuenta :: Eq a => a -> [a] -> Int
cuenta a [] = 0
cuenta a (x:xs) = if a == x
	then 1 + cuenta a xs
	else cuenta a xs


--esPalindromo. Función que verifica si una cadena es palíndromo.
esPalindromo:: Eq a => [a] -> Bool
esPalindromo xs = reversa xs == xs
--Funcion Auxiliar reversa - Recibe una cadena y regresa su inverso, la usaremos para Palindromo
reversa:: [a] -> [a]
reversa [] = []
reversa (x:xs) = reversa xs ++ [x]

--diferencia. Función que devuelve una lista con la diferencia entre
--            dos listas.
diferencia:: Eq a => [a] -> [a] -> [a]
diferencia [] [] = []
diferencia xs [] = []
diferencia [] xs = []
diferencia (x:xs) (y:ys) = if busquedaLista (y:ys) x
	then diferencia xs (y:ys)
	else [x] ++ diferencia xs (y:ys)
--Funcion auxiliar busquedaLista. Recibe una lista y un elemento. Si el elemento está en la lista regresa true
busquedaLista:: Eq a => [a] -> a -> Bool
busquedaLista [] e = False
busquedaLista (x:xs) e = if x == e
	then True
	else busquedaLista xs e

--primos. Función que devuelve una lista con todos los números primos
--        hasta n.
primos :: Int -> [Int]
primos n = [n | n <- [1..n], esPrimo n]
-- Función auxiliar que define si un número es primo o no
esPrimo :: Int -> Bool
esPrimo n = divisores n == [1,n]
--divisores. Función que nos regrsa los divisores de un número en una lista
divisores :: Int -> [Int]
divisores n = [y | y <- [1..n], mod n y==0]

{-- Definición de Binario.--}
data Binario = U | Cero Binario | Uno Binario

--Instancia de la clase Show para Binario.
instance Show Binario where
	show (Uno a) = show a ++ "1"
	show (Cero b) = show b ++ "0"
	show U = "1"

--suma. Función que devuelve la suma de dos Binarios.
suma :: Binario -> Binario -> Binario
suma b U = sucesor b
suma U b = sucesor b
suma (Cero a) (Cero b) = Cero(suma a b)
suma (Uno a) (Cero b) = Uno(suma a b)
suma (Cero a) (Uno b) = Uno(suma a b)
suma (Uno a) (Uno U) = Cero (suma (sucesor a) U)
suma (Uno U) (Uno a) = Cero (suma (sucesor a) U)
suma (Uno (Cero(a))) (Uno (Cero(b))) = Cero(Uno(suma a b))
suma (Uno (Uno(a))) (Uno (Cero(b))) = Cero(Cero(suma (sucesor a) b))
suma (Uno (Cero(a))) (Uno (Uno(b))) = Cero(Cero(suma (sucesor a) b))
suma (Uno (Uno(a))) (Uno (Uno(b))) = Cero(suma (Cero(sucesor a)) (Uno b))
-- Función vista en ayudantía, nos da el sucesor de un número binario
sucesor :: Binario -> Binario
sucesor U = (Cero U)
sucesor (Cero b) = (Uno b)
sucesor (Uno b) = (Cero (sucesor b))

{-- Definición del Árbol binario.--}
-- data Arbol a = Vacio | Nodo a (Arbol a) (Arbol a) deriving(Show)
data Arbol a = Vacio | Nodo a (Arbol a) (Arbol a)

--Instancia de la clase Show para Arbol.
instance Show a => Show (Arbol a) where
    show Vacio = "NIL"
    show (Nodo r i d) = "(" ++ show i ++ ", " ++ show r ++ ", " ++ show d ++ ")"

--inOrden. Función que convierte un árbol binario en una lista por
--         su recorrido in-orden.
inOrden:: Arbol a -> [a]
inOrden Vacio = []
inOrden (Nodo a t1 t2) = inOrden t1 ++ [a] ++ inOrden t2

-- *************************************************RETOS*************************************************
-- Segmento. Nos regresa el segmmento de una lista con los indices que indique el usuario
segmento :: Int -> Int -> [a] -> [a]
segmento a b [] = error "Por favor introduce una lista no vacia"
segmento a b xs = if b <= tamanioLista xs && a > 0
	then segmentoAux a b xs
	else error "Tus indices son incorrectos"
-- segmentoAux
segmentoAux :: Int -> Int -> [a] -> [a]
segmentoAux a b xs = if a <= b then [charAt (a-1) xs] ++ segmentoAux (a+1) b xs else []
-- Te da el tamaño de una lista recibida
tamanioLista:: [a] -> Int
tamanioLista [] = 0
tamanioLista (x:xs) = 1 + tamanioLista xs
-- CharAT - Recibe un entero y una lista (o cadena)
			-- Nos regresa el caracter que resida en el indice recibido
charAt:: Int -> [a] -> a
charAt 0 (x:xs) = x
charAt n (x:xs)= if n < 0 || n > tamanioLista (x:xs)
	then error "No estes molestando"
	else charAt (n-1) xs
