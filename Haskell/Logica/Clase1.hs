module Clase1 where

-- comentarios
{--
	Comentarios de varias lineas
--}
-- Eq -> x==y x/=y
-- Ord -> x> y x<y

--f(x, y) = x*y
prod:: Int -> Int -> Int
prod x y = x*y

fibonacci :: Int -> Int
fibonacci 0 = 0
fibonacci 1 = 1
fibonacci n = fibonacci(n-1) + fibonacci(n-2)
-- Hacen exactamente lo mismo
fib :: Int -> Int
fib n =  case n of
	0 -> 0
	1 -> 1
	m -> fib(m-1) + fib(m-2)

reversa :: String -> String
reversa [] = []
reversa (x:xs) = reversa xs ++ [x]

-- C = {x | 0 <= x <= n}
hasta :: Int -> [Int]
hasta n = [x | x <- [0..n]]

primeros :: [(a,b)] -> [a]
primeros p = [x | (x, _) <- p]

sumaLet :: Int
sumaLet = let x = 3; y = 1 in (x+y)
-- Hacen exactamente lo mismo ambas funciones
sumaW :: Int
sumaW = (x+y) where x = 3; y = 1

absoluto :: Int -> Int
absoluto n
	| n < 0 = (-n)
	| otherwise = n

-- Binario
data Binario = U | Cero Binario | Uno Binario deriving(Show)

--1010
-- Cero (Uno(Cero U )

sucesor :: Binario -> Binario
sucesor U = (Cero U) -- 1 -> 10
sucesor (Cero b) = (Uno b) -- 0  -> 1
sucesor (Uno b) = (Cero (sucesor b)) -- 1 -> 10...

--Árbol binario y condicionales.
data Arbol a = Vacio | Nodo a (Arbol a) (Arbol a)

instance Show a => Show (Arbol a) where
    show Vacio = "Nil"
    show (Nodo r i d) = "(" ++ show i ++ ", " ++ show r ++ ", " ++ show d ++ ")"

-- | insert. Función que inserta un elemento en un árbol.
inserta :: Ord a => a -> Arbol a -> Arbol a
inserta x Vacio = Nodo x (Vacio) (Vacio)
inserta x (Nodo r i d) = if x < r
                        then Nodo r (inserta x i) d
                        else Nodo r i (inserta x d)
