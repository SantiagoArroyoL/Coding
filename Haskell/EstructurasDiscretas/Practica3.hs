{-
Nombre: Arroyo Lozano Santiago
Fecha de Entrega: 18/Octubre/2019
-}
data Var = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | Y | Z deriving (Show, Eq, Ord)    -- < >
data Formula = Prop Var | Neg Formula
              | Formula :&: Formula
              | Formula :|: Formula
              | Formula :=>: Formula
              | Formula :<=>: Formula
              deriving (Show, Eq, Ord)

infixl 9 :&:         -- mayor precedencia 9, menor precedencia 1
infixl 9 :|:
infixr 7 :=>:
infixl 8 :<=>:

--Funcion auxiliar busquedaLista
busquedaLista:: Eq a => [a] -> a -> Bool
busquedaLista [] e = False
busquedaLista (x:xs) e = if x == e
	then True
	else busquedaLista xs e
-- Función Auxiliar Conjunto para que no haya repetidos
aConjunto:: Eq a => [a] -> [a]
aConjunto [] = []
aConjunto (x:xs) = if busquedaLista xs x
   then aConjunto xs
	else [x] ++ aConjunto xs
-- Devuelve una lista con las variables de la fórmula
varListAux :: Formula -> [Var]
varListAux (Prop x) = [x]
varListAux (Neg fs) = varListAux fs
varListAux (Neg fs) = varListAux fs
varListAux (ps:&:qs) = (varListAux ps) ++ (varListAux qs)
varListAux (ps:|:qs) = (varListAux ps) ++ (varListAux qs)
varListAux (xs :=>: fs) = (varListAux xs) ++ (varListAux fs)
varListAux (xs :<=>: ys) = (varListAux xs) ++ (varListAux ys)
--Funcion varList**************
varList:: Formula -> [Var]
varList fs = (aConjunto (varListAux fs))

-- Función negación
negar:: Formula -> Formula
negar (Prop x) = Neg (Prop x)
negar (Neg (Prop x)) = Prop x
negar (Prop x) = Neg (Prop x)
negar (xs :|: ys) = (negar xs) :&: (negar ys)
negar (xs :&: ys) = (negar xs) :|: (negar ys)
negar (xs :=>: ys) =  xs :&: (negar ys)

-- Función equivalencia
equivalencia:: Formula -> Formula
equivalencia (Prop x) = Prop x
equivalencia (xs :=>: ys) = (Neg (xs) :|:  ys)
equivalencia (xs :<=>:ys) = equivalencia (xs :=>: ys) :&: equivalencia (ys :=>: xs)
equivalencia (xs :&: ys) = if xs == ys
						   then equivalencia xs
						   else (equivalencia xs) :&: (equivalencia ys)
equivalencia (xs :|: ys) = if xs == ys
   						   then equivalencia xs
   			   			   else (equivalencia xs) :|: (equivalencia ys)

--Función Auxiliar conjuncion
conjuncion:: Bool->Bool->Bool
conjuncion True True = True
conjuncion True False = False
conjuncion False True = False
conjuncion False False = False
--Función Auxiliar disyuncion
disyuncion:: Bool->Bool->Bool
disyuncion True True = True
disyuncion True False = True
disyuncion False True = True
disyuncion False False = False
--Funcion Auxiliar implicacion
implicacion:: Bool->Bool->Bool
implicacion True True = True
implicacion True False = False
implicacion False True = True
implicacion False False = True
--Funcion Auxiliar Bicondicional
dobleImplica:: Bool->Bool->Bool
dobleImplica True True = True
dobleImplica True False = False
dobleImplica False True = False
dobleImplica False False = True
--Función auxiliar buscarVariable
buscarVariable:: Var -> [(Var,Bool)] -> Bool
buscarVariable x [] = error ("No todas las variables están declaradas")
buscarVariable x ((y,b):ys) = if x == y
   then b
   else buscarVariable x ys
--Función interpretación******************
interp:: Formula -> [(Var,Bool)]-> Bool
interp (Prop x) xs = buscarVariable x xs
interp (Neg xs) ys = not (interp xs ys)
interp (xs :|: ys) zs = if (interp xs zs) || (interp ys zs )
						then True
						else disyuncion (interp xs zs) (interp ys zs)
interp (xs :&: ys) zs = if not (interp xs zs) || (interp ys zs )
					    then True
					    else conjuncion (interp xs zs) (interp ys zs)
interp (xs :=>: ys) zs = if not (interp xs zs)
					     then True
					     else implicacion (interp xs zs) (interp ys zs)
interp (xs :<=>: ys) zs = dobleImplica (interp xs zs) (interp ys zs)

-- Función Combinación************
combinaciones:: Formula -> [[(Var,Bool)]]
combinaciones xs = asignarInterp (varList xs) (combinacionesAux (longitud (varList xs) - 1) [[False],[True]])
--Función Auxiliar longitud
longitud:: (Num b) => [a] -> b
longitud [] = 0
longitud (x:xs) = 1 + longitud xs
--Función Auxiliar combinacionesAux
combinacionesAux:: Int -> [[Bool]] -> [[Bool]]
combinacionesAux 0 xs = xs
combinacionesAux n xs = combinacionesAux (n-1) ((combina xs False) ++ (combina xs True))
--Función Auxiliar combina
combina:: [[Bool]] -> Bool -> [[Bool]]
combina [] b = []
combina (x:xs) b = (b:x):(combina xs b)
--Función Auxiliar asignarInterp
asignarInterp:: [Var] -> [[Bool]] -> [[(Var,Bool)]]
asignarInterp xs [] = []
asignarInterp xs (y:ys) = ((asignarValor xs y):(asignarInterp xs ys))
--Función Auxiliar asignarValor
asignarValor:: [Var] -> [Bool] -> [(Var,Bool)]
asignarValor [] [] = []
asignarValor (x:xs) (y:ys) = (x,y):(asignarValor xs ys)

--Función Tabla de Verdad**********
tablaVerdad:: Formula -> [([(Var,Bool)],Bool)]
tablaVerdad xs = (tablaVerdadAux xs (combinaciones xs))
--Función Auxiliar Tabla de Verdad
tablaVerdadAux:: Formula -> [[(Var,Bool)]] -> [([(Var,Bool)], Bool)]
tablaVerdadAux xs [] = []
tablaVerdadAux xs (y:ys) = (y,(interp xs y)):(tablaVerdadAux xs ys)
