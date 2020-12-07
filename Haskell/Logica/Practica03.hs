{--
Práctica03 - Lógica Computacional
EQUIPO:
 EQUIPO ALFA DINAMITA BUENA ONDA ESCUADRÓN LOBO
INTEGRANTES:
 Arroyo Lozano Santiago - 317150700
 Arévalo Gaytan Rodrigo - 317285880
--}
module Practica03 where

import Practica02


{----- Formas Normales -----}

-- 1. fnn. Función que devuelve la Forma Normal Negativa de una
--         proposición.
fnn :: Prop -> Prop
fnn p = deMorgan(elimImpl(elimEquiv(p)))

-- 2. fnc. Función que devuelve la Forma Normal Conjuntiva de una
--         proposición.
fnc :: Prop -> Prop
fnc p = deMorgan(distribuye(fnn(p)))
-- Función distribuye
-- Función que distribuye las conjunciones y disyunciones siguiendo las reglas de la lógica
--     los últimos dos casos nos servirán para eliminar identidades del tipo   (p V p) y (p ∧ p)
distribuye:: Prop -> Prop
distribuye (PVar x) = PVar x
distribuye (PNeg x) = PNeg x
distribuye (PAnd p (POr xs ys)) = POr (PAnd p xs ) (PAnd p ys)
distribuye (POr p (PAnd xs ys)) = PAnd (POr p xs ) (POr p ys)
distribuye (PAnd (POr xs ys) p ) = POr (PAnd xs p ) (PAnd ys p)
distribuye (POr (PAnd xs ys) p) = PAnd (POr xs p ) (POr ys p)
-- Casos para las identidades:
distribuye (PAnd xs ys) = if xs == ys then distribuye xs else PAnd (distribuye xs) (distribuye ys)
distribuye (POr xs ys) = if xs == ys then distribuye xs else POr (distribuye xs) (distribuye ys)


{----- Algoritmo DPLL -----}

-- Definiciones de algunos conceptos.
type Literal = Prop
type Clausula = [Literal]
type Formula = [Clausula]
type Modelo = [Literal]
type Solucion = (Modelo, Formula)


-- 3. unit. Función que aplica la regla unitaria.
--  (Buscamos una bariable proposicional que esté solita y la pasamos al modelo)
unit :: Solucion -> Solucion
unit (m, []) = (m,[])
unit (m, (y:ys):xs) = if ys == [] then (m ++ [y], elimina (y:ys) xs) else (a, [y:ys] ++ b) where (a,b) = unit (m, xs)
-- Función auxiliar elimina - elimina el elemento recibido de la lista recibida
elimina :: Eq a => a -> [a] -> [a]
elimina x [] = []
elimina x (y:ys) | x == y    = elimina x ys
                 | otherwise = y : elimina x ys

-- 4. elim. Función que aplica la regla de eliminación.
--  (Buscamos todas las clausulas donde aparece la variable, buscamos cada literal en cada clausula antes de eliminar)
elim :: Solucion -> Solucion
elim ([], f) = ([], f)
elim (m, f) = (m, eliminaRep [clausula | clausula<-f, length[literal | literal<-m, (elem literal clausula)]==0])

-- 5. red. Función que aplica la regla de reducción.
red :: Solucion -> Solucion
red ([],f) = ([],f)
red (m, f) = (m, (eliminaRep [ (eliminaVar literal clausula) | clausula<-f, literal<-m,(elem (negar(literal)) clausula)]) ++ (diferencia f [clausula | clausula<-f, literal<-m,(elem (negar(literal)) clausula)]))
--
eliminaVar :: Literal -> Clausula -> Clausula
eliminaVar p q = if elem (negar p) q then (diferencia q [(negar p)]) else q
-- Función negar - Una función que niega la variable dada.
-- En el caso que se reciba una variabla ya negada anteriormente se cancela la doble negación
negar :: Prop -> Prop
negar (PVar p) = (PNeg (PVar p))
negar (PNeg  (PVar p)) = PVar p
--diferencia. Función que devuelve una lista con la diferencia entre
--            dos listas.
diferencia:: Eq a => [a] -> [a] -> [a]
diferencia [] [] = []
diferencia xs [] = []
diferencia [] xs = []
diferencia (x:xs) (y:ys) = if elem x (y:ys)
  then diferencia xs (y:ys)
  else [x] ++ diferencia xs (y:ys)

-- 6. split. Función que aplica la regla de la partición de una literal.
--            Se debe tomar la primer literal que aparezca en la fórmula.
split :: Solucion -> [Solucion]
split (m, []) = []
split (m, (y:ys):xs) = [(m++[y], (y:ys):xs)]++[(m++[negar y], (y:ys):xs)]

-- 7. conflict. Función que determina si la Solucion llegó a una contradicción.
conflict :: Solucion -> Bool
conflict (m, [[]]) = False
conflict ([], []) = False
conflict (m, []) = False
conflict ([], f) = False
conflict ([p], f) = if notElem [negar p] f then False else True
conflict ((z:zs), f) = if conflict([z], f) then True else conflict(zs, f)

-- 8. success. Función que determina si la fórmula es satisfacible.
success :: Solucion -> Bool
success (m, f) = f == []

--9. appDPLL. Función que aplica las reglas anteriores una vez.
-- (primero hacemos unit, despues elim y despues red)
appDPLL :: Solucion -> Solucion
appDPLL (m, f) = red(elim(unit(m, f)))



{-- Puntos Extra --}

--dpll. Función que aplica el algoritmo DPLL a una fórmula.
-- dpll :: Solucion -> Solucion
-- dpll (m, f) = if success (m, f) then (m,f) else dpllAux (m,f)
-- --
-- dpllAux :: Solucion -> Solucion
-- depllAux (m, f) = if conflict (m,f) then (m, f) else
--     if (a,b) == (x,y)
--     then dpll(xs)
--     else dpll(x, y)
-- 	where (a,b) = dpll(m, f) | (x,y) = dpll(a,b) | (xs:ys) = split(m, f)
