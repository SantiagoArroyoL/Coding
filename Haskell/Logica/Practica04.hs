--
--
module Practica04 where

--Definición del tipo de datos para términos.
data Term = V Nombre | F Nombre [Term]

--Definición del tipo de datos para fórmulas.
data Form = NForm | TrueF | FalseF | Pr Nombre [Term] | Eq Term Term |
            Neg Form | Conj Form Form | Disy Form Form |
            Imp Form Form | Equi Form Form | All Nombre Form |
            Ex Nombre Form

type Nombre = String

type Subst = [(Nombre,Term)]


--Instancia Show para Term.
instance Show Term where
  show (V x) = x
  show (F f t) = f ++ "(" ++ show t ++ ")"

--Instancia Show para Form.
instance Show Form where
  show NForm = ""
  show TrueF = "T"
  show FalseF = "F"
  show (Pr p t) = p ++ "(" ++ show t ++ ")"
  show (Eq t1 t2) = "(" ++ show t1 ++ "=" ++ show t2 ++ ")"
  show (Neg f) = "¬" ++ show f
  show (Conj f1 f2) = "(" ++ show f1 ++ " ^ " ++ show f2 ++ ")"
  show (Disy f1 f2) = "(" ++ show f1 ++ " v " ++ show f2 ++ ")"
  show (Imp f1 f2) = "(" ++ show f1 ++ " -> " ++ show f2 ++ ")"
  show (Equi f1 f2) = "(" ++ show f1 ++ " <--> " ++ show f2 ++ ")"
  show (All x f) = "Alle " ++ x ++ " (" ++ show f ++ ")"
  show (Ex x f) = "Ein " ++ x ++ " (" ++ show f ++ ")"


--alcance. Función que devuelve el alcance de los cuantificadores de
--          una fórmula.
alcance :: Form -> [(Form, Form)]
alcance NForm = []
alcance TrueF = []
alcance FalseF = []
alcance (Pr p t) = []
alcance (Eq t1 t2) = []
alcance (Neg f) = alcance f
alcance (Conj f1 f2) = alcance f1 ++ alcance f2
alcance (Disy f1 f2) = alcance f1 ++ alcance f2
alcance (Imp f1 f2) = alcance f1 ++ alcance f2
alcance (Equi f1 f2) = alcance f1 ++ alcance f2
alcance (Ex x f) = [(Ex x (NForm), f)] ++ alcance f
alcance (All x f) = [(All x (NForm),f)] ++ alcance f

--2.-bv. Función que devuelve las variables ligadas de una fórmula.
bv :: Form -> [Nombre]
bv NForm = []
bv TrueF = []
bv FalseF = []
bv (Pr p t) = []
bv (Eq t1 t2) = []
bv (Neg f) = bv f
bv (Conj f1 f2) = bv f1 ++ bv f2
bv (Disy f1 f2) = bv f1 ++ bv f2
bv (Imp f1 f2) = bv f1 ++ bv f2
bv (Equi f1 f2) = bv f1 ++ bv f2
bv (All x f) = if elem x (listaVar f) then [x] ++ bv f else bv f
bv (Ex x f) = if elem x (listaVar f) then [x] ++ bv f else bv f
-- listaVar - Nos regresa una lista con todas las variables en la fórmula
listaVar :: Form -> [Nombre]
listaVar NForm = []
listaVar TrueF = []
listaVar FalseF = []
listaVar (Pr p t) = getNombre t
listaVar (Eq t1 t2) = getNombre [t1] ++ getNombre [t2]
listaVar (Neg f) = eliminaRep(listaVar f)
listaVar (Conj f1 f2) = eliminaRep(listaVar f1 ++ listaVar f2)
listaVar (Disy f1 f2) = eliminaRep(listaVar f1 ++ listaVar f2)
listaVar (Imp f1 f2) = eliminaRep(listaVar f1 ++ listaVar f2)
listaVar (Equi f1 f2) = eliminaRep(listaVar f1 ++ listaVar f2)
listaVar (Ex x f) = eliminaRep(listaVar f)
listaVar(All x f) = eliminaRep(listaVar f)
-- getNombre - Función que nos da el nombre de una variable (De un término).
-- Recibe una lista de términos para los casos de predicados y funciones
getNombre :: [Term] -> [Nombre]
getNombre [] = []
getNombre (y:ys) = getNombreAux y ++ getNombre ys
-- Dividimos los casos Bases en esta función donde no se recibe una lista de términos
getNombreAux :: Term -> [Nombre]
getNombreAux (V x) = [x]
getNombreAux (F x t) = [x] ++ getNombre t

--fv. Función que devuelve las variables libres de una fórmula.
fv :: Form -> [Nombre]
fv f = eliminaRep (diferencia (listaVar f) (bv f))
-- eliminaRep, función que nos ayuda a que no aparezcan las variables
-- de forma repetida.
eliminaRep :: Eq a => [a] -> [a]
eliminaRep [] = []
eliminaRep (x:xs) = if elem x xs then eliminaRep xs else x : eliminaRep xs
--diferencia. Función que devuelve una lista con la diferencia entre
--            dos listaVars.
diferencia:: Eq a => [a] -> [a] -> [a]
diferencia [] [] = []
diferencia xs [] = xs
diferencia [] xs = []
diferencia (x:xs) (y:ys) = if elem x (y:ys)
  then diferencia xs (y:ys)
  else [x] ++ diferencia xs (y:ys)

--sustTerm. Función que realiza la sustitución de variables en un término.
sustTerm :: Term -> Subst -> Term
sustTerm (V x) [] = V x
sustTerm (V x) ((n,t):ts) = if x == n then t else sustTerm (V x) ts
sustTerm (F n t) s = F n (sustTermAux t s)
--sustTermAux
sustTermAux :: [Term] -> Subst -> [Term]
sustTermAux t [] = t
sustTermAux [] s = []
sustTermAux (x:xs) s = [sustTerm x s] ++ sustTermAux xs s

--sustForm. Función que realiza la sustitución de variables en una
--          fórmula sin renombramientos.
sustForm :: Form -> Subst -> Form
sustForm f [] = f
sustForm NForm s = error "No se puede sustituir en una fórmula vacía"
sustForm TrueF s =  error "No se puede sustituir en constantes lógicas"
sustForm FalseF s = error "No se puede sustituir en constantes lógicas"
sustForm (Pr p (t:ts)) s = Pr p (sustTermAux (t:ts) s)
sustForm (Eq t1 t2) s = Eq (sustTerm t1 s) (sustTerm t2 s)
sustForm (Neg f) s = Neg (sustForm f s)
sustForm (Conj f1 f2) s = Conj (sustForm f1 s) (sustForm f2 s)
sustForm (Disy f1 f2) s = Disy (sustForm f1 s) (sustForm f2 s)
sustForm (Imp f1 f2) s = Imp (sustForm f1 s) (sustForm f2 s)
sustForm (Equi f1 f2) s = Equi (sustForm f1 s) (sustForm f2 s)
sustForm (All x f) ((n,t):ts) = if elem n (bv (All x f)) then (sustForm (All x f) ts) else sustForm (All x  (sustForm f [(n,t)])) ts
sustForm (Ex x f) ((n,t):ts) =  if elem n (bv (All x f)) then (sustForm (All x f) ts) else sustForm (All x  (sustForm f [(n,t)])) ts

--alphaEq. Función que dice si dos fórmulas son alpha-equivalentes.
-- alphaEq :: Form -> Form -> Bool
-- alphaEq f1 f2 = (fv f1 == fv f2) && (sonEq f1 f2)

{-- Puntos Extra --}
-- Función que renombra las variables ligadas de una fórmula
-- renom :: Form -> Form
-- renom f = (sustForm f [(n,t) | n <- (bv f), t <- (diferencia (["a".."z"]) (listaVar f))])
dameTerm :: Form -> [Term]
dameTerm NForm = []
dameTerm TrueF = []
dameTerm FalseF = []
dameTerm (Pr p t) = t
dameTerm (Eq t1 t2) = [t1]++[t2]
dameTerm (Neg f) = dameTerm f
dameTerm (Conj f1 f2) = dameTerm f1 ++ dameTerm f2
dameTerm (Disy f1 f2) = dameTerm f1 ++ dameTerm f2
dameTerm (Imp f1 f2) = dameTerm f1 ++ dameTerm f2
dameTerm (Equi f1 f2) = dameTerm f1 ++ dameTerm f2
dameTerm (All x f) = dameTerm f
dameTerm (Ex x f) = dameTerm f
--
-- creaTerm :: [Term] -> Form -> [Term]
-- dameTerm ((V x):xs) f =  if  elem x (listaVar f) then  else [V x] ++ dameTerm xs
-- dameTerm (x:xs) f = [y | y <- filter (notElem l f)]

-- renom f = (sustForm f [(n,t) | n<-(bv f), t<- filter (notElem listaVar f)])
-- renomConj :: Form -> Form
-- sustFormAlpha :: Form -> Subst -> Form
-- sustFormAlpha f s = sustForm (renom f) s
