{--
Práctica01 - Lógica Computacional
EQUIPO:
 EQUIPO ALFA DINAMITA BUENA ONDA ESCUADRÓN LOBO
INTEGRANTES:
 Arroyo Lozano Santiago - 317150700
 Arévalo Gaytan Rodrigo - 317285880
--}
module Practica02 where

--Prop. Tipo de datos para proposiciones lógicas.
data Prop = PTrue | PFalse | PVar String | PNeg Prop | POr Prop Prop
                  | PAnd Prop Prop | PImpl Prop Prop | PEquiv Prop Prop
                  deriving (Eq)
--Estado. Lista de variables asignadas como verdaderas.
type Estado = [String]

--Instancia Show para Prop.
instance Show Prop where
  show PTrue = "true"
  show PFalse = "false "
  show (PVar x) = show x
  show (PNeg p) = "¬"++ (show p)
  show (POr p1 p2) = "(" ++ show p1 ++ " v " ++ show p2 ++ ")"
  show (PAnd p1 p2) = "(" ++ show p1 ++ " ^ " ++ show p2 ++ ")"
  show (PImpl p1 p2) = "(" ++ show p1 ++ " -> " ++ show p2 ++ ")"
  show (PEquiv p1 p2) = "(" ++ show p1 ++ " <--> " ++ show p2 ++ ")"


--1. interp. Función que evalua una proposición dado el estado.
interp :: Estado -> Prop -> Bool
interp e PTrue = True
interp e PFalse = False
interp e (PVar p) = elem p e
interp e (PNeg p) = if (interp e p) == True then False else True
interp e (POr p1 p2) = (interp e p1) || (interp e p2)
interp e (PAnd p1 p2) = (interp e p1) && (interp e p2)
interp e (PImpl p1 p2) = if ((interp e p1) == True) && ((interp e p2) == False) then False else True
interp e (PEquiv p1 p2) = if (interp e p1) == (interp e p2) then True else False

--2. estados. Función que devuelve una lista de todas las combinaciones
-- 				posibles de los estados de una proposición.
estados :: Prop -> [Estado]
estados PTrue = []
estados PFalse = []
estados (PVar p) = subconj [p]
estados (PNeg p) = subconj (vars p)
estados (POr p1 p2) = subconj (vars (POr p1 p2))
estados (PAnd p1 p2) = subconj (vars (PAnd p1 p2))
estados (PImpl p1 p2) = subconj (vars (PImpl p1 p2))
estados (PEquiv p1 p2) = subconj (vars (PEquiv p1 p2))

--3. vars. Función que obtiene la lista de todas las variables de una
--			proposición.
vars :: Prop -> [String]
vars (PTrue) = []
vars (PFalse) = []
vars (PVar p) = [p]
vars (PNeg p) = eliminaRep(vars p)
vars (POr p1 p2) = eliminaRep((vars p1) ++ (vars p2))
vars (PAnd p1 p2) = eliminaRep((vars p1) ++ (vars p2))
vars (PImpl p1 p2) = eliminaRep((vars p1) ++ (vars p2))
vars (PEquiv p1 p2) = eliminaRep((vars p1) ++ (vars p2))
-- eliminaRep, función que nos ayuda a que no aparezcan las variables
-- de forma repetida.
eliminaRep :: Eq a => [a] -> [a]
eliminaRep [] = []
eliminaRep (x:xs) = if elem x xs then eliminaRep xs else x : eliminaRep xs

--4. subconj. Función que devuelve el conjunto potencia de una lista.
subconj :: [a] -> [[a]]
subconj [] = [[]]
subconj (x:xs) = [x:ys | ys <- (subconj xs)] ++ (subconj xs)

--5. modelos. Función que devuelve la lista de todos los modelos posibles
-- 				para una proposición.
modelos :: Prop -> [Estado]
modelos p = [i | i <- estados p, interp i p]

--6. tautologia. Función que dice si una proposición es tautología.
-- Usamos la función and, que recibe una lista de booleanos y los evalúa usando el operador and (valga la redundancia)
-- Y así, todos los elementos tienen que ser verdaderos para que la función de verdadero
tautologia :: Prop -> Bool
tautologia (PTrue) = False
tautologia (PFalse) = True
tautologia (PVar p) = and [interp e (PVar p) | e <- estados (PVar p)]
tautologia (PNeg p) = and [interp e (PNeg p) | e <- estados (PNeg p)]
tautologia (POr p1 p2) = and [interp e (POr p1 p2) | e <- estados (POr p1 p2)]
tautologia (PAnd p1 p2) = and [interp e (PAnd p1 p2) | e <- estados (PAnd p1 p2)]
tautologia (PImpl p1 p2) = and [interp e (PImpl p1 p2) | e <- estados (PImpl p1 p2)]
tautologia (PEquiv p1 p2) = and [interp e (PEquiv p1 p2) | e <- estados (PEquiv p1 p2)]

--7. satisfen. Función que resuelve si una proposición es satisfacible
-- 				con cierto estado.
satisfen :: Estado -> Prop -> Bool
satisfen e p = interp e p

--8. satisf. Función que resuelve si una proposición es satisfacible.
satisf :: Prop -> Bool
satisf p = not (contrad p)

--9. insatisfen. Función que resuelve si una proposición es insatisfacible
-- 					con cierto estado.
insatisfen :: Estado -> Prop -> Bool
insatisfen e p = not (interp e p)

--10. contrad. Función que dice si una proposición es una contradicción.
-- Usamos la función and, que recibe una lista de booleanos y los evalúa usando el operador and (valga la redundancia)
-- Y así, todos los elementos tienen que ser falsos para que la función de verdadero
contrad :: Prop -> Bool
contrad (PTrue) = False
contrad (PFalse) = True
contrad (PVar p) = and [not (interp e (PVar p)) | e <- estados (PVar p)]
contrad (PNeg p) = and [not (interp e (PNeg p)) | e <- estados (PNeg p)]
contrad (POr p1 p2) = and [not (interp e (POr p1 p2)) | e <- estados (POr p1 p2)]
contrad (PAnd p1 p2) = and [not (interp e (PAnd p1 p2)) | e <- estados (PAnd p1 p2)]
contrad (PImpl p1 p2) = and [not (interp e (PImpl p1 p2)) | e <- estados (PImpl p1 p2)]
contrad (PEquiv p1 p2) = and [not (interp e (PEquiv p1 p2)) | e <- estados (PEquiv p1 p2)]

--11. equiv. Función que devuelve True si dos proposiciones son equivalentes.
equiv :: Prop -> Prop -> Bool
equiv p1 p2 = modelos p1 == modelos p2

--12. elimEquiv. Función que elimina las equivalencias lógicas.
elimEquiv :: Prop -> Prop
elimEquiv (PTrue) = (PTrue)
elimEquiv (PFalse) = (PFalse)
elimEquiv (PVar p) = (PVar p)
elimEquiv (PNeg p) = (PNeg (elimEquiv p))
elimEquiv (POr p1 p2) = (POr (elimEquiv p1) (elimEquiv p2))
elimEquiv (PAnd p1 p2) = (PAnd (elimEquiv p1) (elimEquiv p2))
elimEquiv (PImpl p1 p2) = (PImpl (elimEquiv p1) (elimEquiv p2))
elimEquiv (PEquiv p1 p2) = (PAnd (PImpl (elimEquiv p1) (elimEquiv p2)) (PImpl (elimEquiv p2) (elimEquiv p1)))

--13. elimImpl. Función que elimina las implicaciones lógicas.
elimImpl :: Prop -> Prop
elimImpl (PTrue) = (PTrue)
elimImpl (PFalse) = (PFalse)
elimImpl (PVar p) = (PVar p)
elimImpl (PNeg p) = (PNeg (elimImpl p))
elimImpl (POr p1 p2) = (POr (elimImpl p1) (elimImpl p2))
elimImpl (PAnd p1 p2) = (PAnd (elimImpl p1) (elimImpl p2))
elimImpl (PImpl p1 p2) = (POr (PNeg (elimImpl p1)) (elimImpl p2))
elimImpl (PEquiv p1 p2) = (PEquiv (elimImpl p1) (elimImpl p2))

-- | 14. Función que aplica las leyes de De Morgan.
deMorgan :: Prop -> Prop
deMorgan PTrue = PTrue
deMorgan PFalse = PFalse
deMorgan (PVar a) = (PVar a)
deMorgan (PNeg (PVar a)) = (PNeg (PVar a))
deMorgan (PNeg (POr a b)) = (PAnd (deMorgan (PNeg a)) (deMorgan (PNeg b)))
deMorgan (PNeg (PAnd a b)) = (POr (deMorgan (PNeg a)) (deMorgan (PNeg b)))
deMorgan (PAnd a b) = (PAnd (deMorgan a) (deMorgan b))
deMorgan (POr a b) = (POr (deMorgan a) (deMorgan b))

{-- Punto extra--}
{-- FUNCIONES AUXILIARES USADAS
Usamos la función "all" de haskell. Escencialmente lo que hace es verificar si cada elemento
	dentro de la lista (segundo parámetro) cumple con la condición dada en el primer parámetro.
	Manda true si todos los elementos la cumplen, false en caso contrario

También usamos la función "any" de haskell. Escencialmente revisa si al menos un elemento
	dentro de la lista (segundo parámetro) cumple con la condición dada en el primero parámetro.
	Manda true si al menos un elemento la cumple, false en caso contrario
--}

-- 1.1 Función que te muestra los estados de cada variable proposicional dentro del conjunto
estadosConj :: [Prop] -> [Estado]
estadosConj [] = []
estadosConj (x:xs) = eliminaRep(estados x ++ estadosConj xs)

-- 1.2 Función que devuelve la lista de todos los modelos posibles para una proposición.
-- Mostraremos el o los modelos que cumplan con todas las proposiciones del conjunto al mismo tiempo
modelosConj :: [Prop] -> [Estado]
modelosConj [] = []
modelosConj (x:xs) = eliminaRep(modelos x ++ modelosConj xs)
----------------------- INTENTOS FALLIDOS ------------------
-- modelosConj (x:xs) = modelos x ++ modelosConj xs
-- modelosConj (x:xs) = [interseccion x1 x2 | x1 <- modelos x, x2 <- modelosConj xs]
-- modelosConj (x:xs) = eliminaNoRep(modelos x ++ modelosConj xs)
-----------------------------------------------------------
-- Función auxiliar Interseccion
-- Funciona tal cual la intersección entre conjuntos
-- De dos listas tomadas nos quedaremos sólo con los elementos que tengan en común
interseccion:: Eq a => [a] -> [a] -> [a]
interseccion [] [] = []
interseccion xs [] = []
interseccion [] xs = []
interseccion (x:xs) (y:ys) = if elem x (y:ys)
    then eliminaRep([x] ++ interseccion xs (y:ys))
    else interseccion xs (y:ys)


-- 1.3 Función que resuelve si un conjunto de proposiciones es satisfacible con cierto estado.
-- Usamos la función "all" de Haskell
-- En este caso revisamos que todos los elementos de la lista gamma sean satisfacibles con el estado e
satisfenConj:: Estado -> [Prop] -> Bool
satisfenConj e gamma = all (satisfen e) gamma

-- 1.4 Función que resuelve si un conjunto de proposiciones es satisfacible.
-- Usamos la función "all" de Haskell
-- En este caso revisamos que todos los elementos de la lista gamma sean satisfacibles
satisfConj:: [Prop] -> Bool
satisfConj gamma = all (satisf) gamma

-- 1.5 Función que resuelve si un conjunto de proposiciones es insatisfacible con cierto estado.
-- Usamos la función "any" de Haskell
-- En este caso revisamos que al menos ún elemento sea insatisfacible con el estado dado
insatisfenConj:: Estado -> [Prop] -> Bool
insatisfenConj e gamma = any (insatisfen e) gamma

-- 1.6 Función que resuelve si un conjunto de proposiciones es insatisfacible
insatisfConj:: [Prop] -> Bool
insatisfConj gamma = not(satisfConj gamma)

--consecuencia. Función que determina si una proposición es consecuencia
--				del conjunto de premisas.
consecuencia:: [Prop] -> Prop -> Bool
consecuencia gamma phi = null [i | i <- estadosConj (phi : gamma),
                                satisfenConj i gamma,
                                not (satisfen i phi)]

--argCorrecto. Función que determina si un argumento es lógicamente
--				correcto dadas las premisas.
argCorrecto :: [Prop] -> Prop -> Bool
argCorrecto gamma psi = consecuencia gamma psi
