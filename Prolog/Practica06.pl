% 2.- MUNDO DE CUBOS - los definimos como dinamicos pues los vamos a estar moviendo.
:- dynamic(sobre/2).
:- dynamic(bloqueado/1).
% sobre(X,Y) - X está sobre Y
sobre(gris,rojo).
sobre(rojo,azul).
sobre(amarillo,rosa).
% hastaArriba(X) - X es el cubo más arriba en su pila de cubos.
hastaArriba(X) :- not(bloqueado(X)).
%  bloqueado(X) - X tiene un cubo encima
bloqueado(rojo).
bloqueado(azul).
bloqueado(rosa).
% hastaAbajo(X) - X es el cubo que se encuentre hasta el fondo de su pila de cubos.
hastaAbajo(X) :- not(sobre(X,_)).
% mover(X,Y) - nos permite mover X sobre Y si este último esta encima.
mover(X,Y) :- sobre(Y,X), !, assert(bloqueado(Y)),retract(sobre(Y,X)),revisa(X,Y), intercambia(X,Y).
% revisa(X,Y) - relación auxiliar que revisa si al mover el cubo este se debe bloquear o no
revisa(X,Y) :- sobre(Z,Y), !, assert(sobre(Z,X)), assert(bloqueado(X)); retract(bloqueado(X)).
% intercambia(X,Y) - relación auxiliar que intercambia el cubo debajo del original si es debido
intercambia(X,Y) :- sobre(X,Z), !, assert(sobre(Y,Z)), retract(sobre(X,Z)), assert(sobre(X,Y)); assert(sobre(X,Y)).


% 3.-AUTÓMATA
qi(q0).
qf(q0).
% Transición
delta(q0,a,q1).
delta(q1,b,q2).
delta(q2,a,q0).
delta(q2,a,q3).
delta(q2,a,q4).
delta(q3,a,q0).
delta(q4,a,q3).
% Primero preguntamos si existe la transición introducia con el estado inicial
aceptar([X|XS]) :- delta(Z,X,_), qi(Z), !, recursion(Z,[X|XS],_).
% Recursivamente seguimos buscando el camino mientras vaciamos la lista
recursion(S, [], [S]) :- qf(S).
recursion(S,[X|XS],[S|SS]) :- delta(S,X,Y), recursion(Y, XS, SS).


% 4.- MEZCLAR
mezclar(Lista, Lista, []).
mezclar(Lista, [], Lista).
mezclar([X|ZS], [X|XS], [Y|YS]) :- X =< Y, mezclar(ZS,XS,[Y|YS]).
mezclar([Y|ZS], [X|XS], [Y|YS]) :- Y =< X, mezclar(ZS,[X|XS],YS).

% 5.- PUNTO EXTRA
% 5.1.- enOrden
enOrden(X,Y) :- hastaArriba(X), hastaArriba(Y), !, buscaAbajo(X,Z), assert(sobre(Z,Y)), assert(bloqueado(Y)).
% Auxiliar que busca el más bajo en la pila de X
buscaAbajo(Y,Y) :- hastaAbajo(Y).
buscaAbajo(X,Y) :- sobre(X,Z), buscaAbajo(Z,Y).
