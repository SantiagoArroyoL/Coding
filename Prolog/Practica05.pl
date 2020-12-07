/*
Practica05 - Lógica Computacional
EQUIPO:
    EQUIPO ALFA DINAMITA BUENA ONDA ESCUADRÓN LOBO
INTEGRANTES:
Arroyo Lozano Santiago - 317150700
Arévalo Gaytán Rodrigo - 317285880
*/

/* 1.-elem. función que nos dice si el elemento que le pasamos se encuentra en una lista*/
elem(X,[X|_]). /* Caso base */
elem(X,[_|L]) :- elem(X,L).

/* 2.-suma. función que nos regresa la suma de todos los elementos de la lista*/
suma([],0).
suma([X|Y],N) :- suma(Y,M), N is X+M.

/* 3.-palindromo. función que nos dice si una lista es palindromo*/
palindromo(XS) :- XS = L, reversa(XS,L).

/* 3.1.-reversa. función que nos regresa la reversa de una lista*/
reversa([],[]).
reversa([X|XS],YS) :- reversa(XS,ZS),conc(ZS,[X],YS).

/* 3.2.-conc. función que nos regresa dos listas concatenadas*/
conc([],XS,XS).
conc([X|XS],YS,[X|ZS]) :- conc(XS,YS,ZS).

/* 4.-ocurrir. función que nos regresa el número de veces que aparece un elemento en una lista*/
ocurrir(_,[],0).
ocurrir(X,[Y],0) :- X \= Y.
ocurrir(X,[Y],1) :- X = Y.
ocurrir(X,[Y|YS],N) :- ocurrir(X,[Y],L), ocurrir(X,YS,M), N is L+M.

/* 5.1.-ser. Relación reflexiva de ser un gato */
ser(queso,queso).
ser(shadow,shadow).

/* 5.2.1.-amigo Relación de que un gato es amigo de otro */
amigo(shadow,queso).
amigo(queso,shadow).

/* 5.2.2-amigos. Relación simétrica de dos gatos que son amigos */
amigos(X,Y) :- ser(X,X),ser(Y,Y),amigo(X,Y).
amigos(X,Y) :- ser(X,X),ser(Y,Y),amigo(Y,X).

/*5.3.-masgrande. Relación transitiva entre dos gatos denotando que uno es más grande que otro */
masgrande(shadow,queso).
masgrande(queso,lola).
masgrande(A,C) :- masgrande(A,B), masgrande(B,C), ser(A,A), ser(C,C).

/* 6.- in_order. función que nos regresa un arbol en su forma in orden*/
% in_order(tree(X,empty, empty), X).
% in_order(tree(X,Y, empty), L):- in_order(Y,L).
% in_order(tree(X,empty,Z), R):- in_order(Z,R).
in_order(tree(X,_,_), X).
in_order(tree(_,L,_), X) :- inorder(L,X).
in_order(tree(_,_,R), X) :- inorder(R,X).

/*7.- Implementamos varios hechos para poder definir la relación 'abuelo' como se nos pide

	Definamos primero algunas cosas:

	Predicados (Relaciones):
	abuelo(x,y) x es abuelo de y
	padre_hijo(x,y) x es padre de y

	Constantes:
	autor - El autor del texto
	mujero - La mujer del autor
	hija - La hija original del autor
	padre - El padre biológico del autor
	hermana - La hermana biológica del autor
	hijo - El hijo biológico del autor
*/

% Escribamos sólo las relaciones(hechos) padre-hijo:
padre_hijo(padre,autor).
padre_hijo(autor,hija).
padre_hijo(autor,hijo).
padre_hijo(padre,hermana).
padre_hijo(autor,padre).

abuelo(A,C) :- padre_hijo(A,B), padre_hijo(B,C).
