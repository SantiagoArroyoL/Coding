--Bonilla Ruiz Roberto Adrian
data Var = A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z deriving(Show,Eq,Ord)

data Formula = Prop Var | Neg Formula
			   |Formula :&: Formula
			   |Formula :|: Formula
			   |Formula :=>: Formula
			   |Formula :<=>: Formula
			   deriving(Show,Eq,Ord)

infixl 9 :&:
infixr 9 :|:
infixr 7 :=>:
infixl 8 :<=>:


busquedaLista :: Eq a => [a] -> a -> Bool
busquedaLista [] e = False
busquedaLista (x:xs) e = if x == e
			then True
			else busquedaLista xs e

aConjunto :: Eq a => [a] -> [a]
aConjunto [] = []
aConjunto (x:xs) = if  busquedaLista xs x
				   then aConjunto xs
				   else [x] ++ aConjunto xs

varList::Formula -> [Var]
varList (Prop x) = [x]
varList (Neg fs) = varList fs
varList (ps :&: qs) =aConjunto((varList ps) ++ (varList qs))
varList (ps :<=>: qs) =aConjunto((varList ps) ++ (varList qs))
varList (ps :|: qs) =aConjunto((varList ps) ++ (varList qs))
varList (ps :=>: qs) =aConjunto((varList ps) ++ (varList qs))


negar:: Formula -> Formula
negar (Prop x) = Neg (Prop x)
negar (Neg xs) = xs
negar (xs :|: ys) = (negar xs):&:(negar ys)
negar (xs :&: ys) = (negar xs):|:(negar ys)
negar (xs :=>: ys) = (xs :&: negar(ys))
negar (xs :<=>: ys) = negar(xs :=>: ys) :|: negar(ys :=>: xs)





equivalencia :: Formula -> Formula
equivalencia (Prop x) = Prop x
equivalencia (Neg (Prop p)) = (Neg (Prop p))
equivalencia (Neg xs) = negar (equivalencia xs)
equivalencia (xs :&: ys) =
						if xs == ys
						then equivalencia xs
						else (equivalencia xs) :&: (equivalencia ys)

equivalencia (xs :|: ys) =
						  if xs == ys
						  then equivalencia xs
						  else (equivalencia xs) :|: (equivalencia ys)

equivalencia (xs :=>: ys) = negar(equivalencia xs) :|: (equivalencia ys)

equivalencia (xs :<=>: ys) = equivalencia(xs :=>: ys) :&: equivalencia(ys :=>: xs)

no :: Bool -> Bool
no True = False
no False = True

traerValor::Var->[(Var,Bool)]->Bool
traerValor  a [] = error "No todas las variables están definidas"
traerValor  a ((p,v):xs) =
						if a==p
						then v
						else traerValor a xs



interp :: Formula -> [(Var,Bool)] -> Bool
interp (Prop x) ys =  (traerValor x ys)
interp (Neg xs) ys = no (interp xs ys)
interp (xs :&: ys) ft =  (interp xs ft)&&(interp ys ft)


interp (xs :|: ys) ft = (interp xs ft)||(interp ys ft)

interp (xs :=>: ys) ft = (not(interp xs ft))||(interp ys ft)

interp (xs :<=>: ys) ft = (interp (xs :=>: ys) ft) && (interp(ys :=>: xs) ft)

combina :: [[Bool]]->Bool->[[Bool]]
combina [] b = []
combina (x:xs) b = (b:x):(combina xs b)

combinacionesAux :: Int->[[Bool]]->[[Bool]]
combinacionesAux 0 xs = xs
combinacionesAux n xs = combinacionesAux (n-1)
						((combina xs False) ++ (combina xs True))

asignarValor :: [Var]->[Bool]->[(Var,Bool)]
asignarValor [] [] = []
asignarValor (x:xs) (y:ys) = (x,y):(asignarValor xs ys)

asignarInterp::[Var]->[[Bool]]->[[(Var,Bool)]]
asignarInterp xs [] = []
asignarInterp xs (y:ys)= ((asignarValor xs y) : asignarInterp xs ys)

longitud :: [a] -> Int
longitud [] = 0
longitud (_:xs) = longitud xs +1

combinaciones :: Formula -> [[(Var,Bool)]]
combinaciones xs =
	asignarInterp
					(varList xs)
					(combinacionesAux ((longitud (varList xs))-1) [[False],[True]])

tablaVerdad :: Formula->[([(Var,Bool)], Bool)]
tablaVerdad xs = (tablaVerdadAux xs (combinaciones xs))

tablaVerdadAux :: Formula ->[[(Var,Bool)]]->[([(Var,Bool)],Bool)]
tablaVerdadAux xs [] = []
tablaVerdadAux xs (y:ys) = (y,(interp xs y)):(tablaVerdadAux xs ys)
