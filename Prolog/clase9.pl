hombre(bruno).
hombre(miguel).
mujer(fer).


comer(miguel, chocolate).
comer(miguel, papas).
comer(miguel, doritos).

comida(X) :- comer(_, X).

hoy(martes).
% mañana(miercoles) :- hoy(martes).

padres(tom, bruno).
padres(judy, bruno).

padres(toby, miguel).
padres(jess, miguel).

hermano(X, Y) :- hombre(X), padres(Z, X), padres(Z, Y).

ultimo([X], X).
ultimo([_|XS], Y) :- ultimo(XS, Y).

longitud([], 0).
longitud([_|XS], N) :- longitud(XS, M), N is M + 1.

add(X, empty, tree(X, empty, empty)).
add(X, tree(Y, L, R), tree(Y, L1, R)) :- X =< Y, add(X, L, L1).
add(X, tree(Y, L, R), tree(Y, L, R1)) :- X > Y, add(X, R, R1).
