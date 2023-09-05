{-- Práctica02 - Automatas y Lenguajes Formales
 Arroyo Lozano Santiago - 317150700
 Arévalo Gaytan Rodrigo - 317285880
--}
data Edo = Q0 | Q1 | Q2 | Q3 | QF deriving Show
type Q = [Edo]

data Simbolo = A | B | X | Y | Blanco deriving Show