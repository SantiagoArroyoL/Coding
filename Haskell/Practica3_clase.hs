
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


-- Devuelve una lista con las variables de la fórmula
varList :: Formula -> [Var]
varList (Prop x) = [x]
varList (Neg fs) = varList fs

{-
varList (ps:&:qs) = (varList ps)++
                    (varList qs)


varList (Prop P :=>: Neg((Prop Q :<=>: Prop W):&:Neg(Prop P)))  -- *

varList (Prop P :=>: Neg(*)
varList (Prop P) ++
varList (Neg (*))

varList (Prop P) = [P]
varList (Neg (*)) = varList *
varList (Prop Q :<=>: Prop W):&:Neg(Prop P))
varList (Prop Q :<=>: Prop W) ++
varList Neg(Prop P))

varList (Prop Q :<=>: Prop W)
varList (Prop Q) ++
varList (Prop W)
varList (Prop Q) = [Q]
varList (Prop W) = [W]
varList (Neg (Prop P)) = varList (Prop P)
varList (Prop P) = [P]
[P, Q, W]

Orden lexicografico 0 | 1 | ... | n

-}
