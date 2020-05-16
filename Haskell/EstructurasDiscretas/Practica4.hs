{-
 * Arroyo Lozano Santiago
 * Práctica 4 Haskell
 * Digraficas


 ** Hola Luis, kruskal tiene un problema. El primer arista que debería formar el arbol a veces se lo salta,
 * en casos cuando dicho arista es el primero de la lista,etc. Pero hay veces en los que kruskal funciona a
 * la perfección, de hecho te entregué hasta el domingo la practica porque estaba intentando resolver dicho
 * problema pero nomás no. Con un 15 alcanzo el 9 en final entonces por lo menos un punto de 3 de kruskal
 * consigo ese promedio, las demás funcionan a la perfección incluyendo los puntos extras, entonces, lo dejo
 * a tu criterio,  pero bueno gracias por todo Luis, lindo fin de año, nos vemos pronto.
-}

type Grafica = ([Integer],[(Integer,Integer,Float)])

--------------------------------------------------------------------------------------------------------------------------------------------
-----------------------------------------------------------FUNCIONES AUXILIARES GENERALES---------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------------------------

--reversa
reversa:: [(Integer,Integer,Float)] -> [(Float,Integer,Integer)]
reversa [] = []
reversa ((x,y,z):xs) = [(z,y,x)] ++ reversa xs

--Lo contrario a reversa
versa:: [(Float,Integer,Integer)] -> [(Integer,Integer,Float)]
versa [] = []
versa ((z,y,x):xs) = [(x,y,z)] ++ versa xs

-- Pertenece
pertenencia :: Eq a => a -> [a] -> Bool
pertenencia elem [] = False
pertenencia elem (x:xs) = if elem == x
                          then True
                          else pertenencia elem xs

--Ordenamiento
quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = quicksort [y | y <- xs, y <= x] ++ [x] ++ quicksort [y | y <- xs, y > x]

--Funcion Auxiliar - funcion que devuelve el peso de una arista
peso:: (Integer,Integer,Float) -> Float
peso (x,y,z) = z

--Funcion Auxiliar
comparacionSinPeso:: (Integer,Integer,Float) -> (Integer,Integer,Float) -> Bool
comparacionSinPeso (x,y,z) (q,w,e) = if x == q && y == w
                                     then True
                                     else False

--Funcion que busca un entero en la lista de enteros
buscar:: [Integer] -> Integer -> Bool
buscar [] e = False
buscar (x:xs) e = if x == e
                         then True
                         else buscar xs e
--Función que busca un arista en la lista de aristas
buscarArista:: [(Integer,Integer,Float)] -> (Integer,Integer,Float) -> Bool
buscarArista [] e = False
buscarArista (x:xs) e = if x == e
                         then True
                         else False

--generador de peso (solo pasa de integer a float)
generadorPeso:: Integer -> Float
generadorPeso y = fromInteger y :: Float

--Función que nos da el largo de una lista
long:: [a] -> Integer
long [] = 0
long (x:xs) = long xs + 1

--Funcion que recibe un arista y devuelve su primer vértice
devuelveNodo:: (Integer,Integer,Float) -> Integer
devuelveNodo (x,y,z) = x

--Funcion que recibe un arista y devulve su incidencia.
devuelveIncidencia:: (Integer,Integer,Float) -> Integer
devuelveIncidencia (x,y,z) = y

--Funcion que devuelve la incidencia del arista
devInciList:: [(Integer,Integer,Float)] -> (Integer,Integer,Float)
devInciList (x:xs) = x

--Función que quita elementos repetidos de una lista de enteros
quitarRepetidos:: [Integer] -> [Integer]
quitarRepetidos [] = []
quitarRepetidos (x:xs) = if buscar xs x
                         then quitarRepetidos xs
                         else (x:(quitarRepetidos xs))

--Función que quita aristas repetidos
quitarAristasRepetidos:: [(Integer,Integer,Float)] -> [(Integer,Integer,Float)]
quitarAristasRepetidos [] = []
quitarAristasRepetidos (x:xs) = if buscarArista xs x
                                then quitarAristasRepetidos xs
                                else (x:(quitarAristasRepetidos xs))

--Funcion Auxiliar que elimina el dominio repetido
dominioRepetido:: Grafica -> [Integer]
dominioRepetido ([],[]) = []
dominioRepetido (xs,[]) = []
dominioRepetido (xs,y:ys) = ((devuelveNodo y):dominioRepetido (xs,ys))

-- Funcion Auxiliar que devuelve una lista con todos las aristas reflexivas según el dominio
generaReflex:: [Integer] -> [(Integer,Integer,Float)]
generaReflex [] = []
generaReflex (x:xs) = [(x,x,generadorPeso x)] ++ generaReflex xs

--Funcion Auxiliar - funcion que busca una arista en una lista de aristas
buscadorArista :: [(Integer,Integer,Float)] -> (Integer,Integer,Float) -> Bool
buscadorArista [] e = False
buscadorArista (x:xs) e = if comparacionSinPeso x e
    then True
    else buscadorArista xs e

-- FUNCION auxiliar que devuelve una lista con los elementos que no estan en la segunda lista pero si en la primera
quitarElementos:: [(Integer,Integer,Float)] -> [(Integer,Integer,Float)] -> [(Integer,Integer,Float)]
quitarElementos [] ys = []
quitarElementos (x:xs) ys = if buscadorArista ys x
                                then [] ++ quitarElementos xs ys
                                else [x] ++ quitarElementos xs ys

--Funcion Auxiliar
numerosRepetidos:: [Integer] -> Integer -> Integer
numerosRepetidos [] e = 0
numerosRepetidos (x:xs) e = if e == x
    then 1 + numerosRepetidos (xs) e
    else numerosRepetidos (xs) e

--Funcion Auxiliar que busca los repetidos
busquedaRepetido:: [Integer] -> [Integer] -> Integer
busquedaRepetido [] xs = 0
busquedaRepetido xs [] = 0
busquedaRepetido xs (y:ys) =  numerosRepetidos (xs) y + busquedaRepetido xs ys

--Función auxiliar que nos devuelve el dominio de la relacion
devuelveDominio:: [(Integer,Integer,Float)] -> [Integer]
devuelveDominio [] = []
devuelveDominio (x:xs) = [devuelveNodo x] ++ devuelveDominio xs

--Funcion Auxiliar - que devuelve la adyacencia de una arista
busquedaAdyacencia:: (Integer,Integer,Float) -> Integer -> [Integer]
busquedaAdyacencia (x,y,z) e =  if e == x
                                then [y]
                                else []

--Funcion que cuenta
masDeUno:: [(Integer,Integer,Float)] -> Bool
masDeUno [] = False
masDeUno (x:xs) = if xs == []
                  then True
                  else False

--FUNCION AUXILIAR  que quita las aristas repetidas de una lista
quitarAristasRepetidas :: [(Integer,Integer,Float)] -> [(Integer,Integer,Float)]
quitarAristasRepetidas [] = []
quitarAristasRepetidas (x:xs) = if buscadorArista xs x
                                then quitarAristasRepetidas xs
                                else (x:quitarAristasRepetidas xs)

--------------------------------------------------------------------------------------------------------------------------------------------
----------------------------------------------------------FIN DE AUXILIARES-----------------------------------------------------------------
--------------------------------------------------------------------------------------------------------------------------------------------

--Función INICIDENCIAS
incidencias:: Grafica -> Integer -> [Integer]
incidencias ([],ys) x = error ("Se ingreso una grafica vacia")
incidencias (xs,[]) y = []
incidencias (xs,y:ys) e = quitarRepetidos((busquedaIncidencia y e) ++ incidencias (xs,ys) e)
--Funcion Auxiliar - que devuelve la incidencia de una arista
busquedaIncidencia:: (Integer,Integer,Float) -> Integer -> [Integer]
busquedaIncidencia (x,y,z) e =  if e == y
                                then [x]
                                else []


-- FUNCION ADYACENCIAS
adyacencias:: Grafica -> Integer -> [Integer]
adyacencias ([],ys) x = error ("Se ingreso una grafica vacia")
adyacencias (xs,[]) y = []
adyacencias (xs,y:ys) e = quitarRepetidos((busquedaAdyacencia y e) ++ adyacencias (xs,ys) e)


--FUNCION INGRADO
ingrado:: Grafica -> Integer -> Integer
ingrado ([],ys) x = error ("Se ingreso una grafica vacia")
ingrado (xs,[]) y = 0
ingrado (xs,ys) e = long(incidencias (xs,ys) e )


--FUNCION EXGRADO (trayectorias)
trayectorias:: Grafica -> Integer -> Integer
trayectorias ([],ys) x = error ("Se ingreso una grafica vacia")
trayectorias (xs,[]) y = 0
trayectorias (xs,ys) e = long(adyacencias (xs,ys) e )


--FUNCION KRUSKAL
kruskal:: Grafica -> Grafica
kruskal (xs,ys) = (xs, kruskalAux ys)
--Función Auxiliar que revisa los aristas y forma el árbol
kruskalAux:: [(Integer,Integer,Float)] -> [(Integer,Integer,Float)]
kruskalAux [] = []
kruskalAux (y:ys) = if perteneceNodo y (comparacionConPeso (y:ys))
                    then [] ++ kruskalAux ys
                    else [y] ++ kruskalAux ys
--Funcion que ordena los aristas conforme a su peso
comparacionConPeso:: [(Integer,Integer,Float)] -> [(Integer,Integer,Float)]
comparacionConPeso xs = versa (quicksort (reversa xs))
--Elimina repetidos
aConjunto :: Eq a => [a] -> [a]
aConjunto [] = []
aConjunto (x:xs) = if pertenencia x xs
                   then aConjunto xs
                   else (x:(aConjunto xs))
-- cambia las adya
lsAdya :: [(Integer,Integer,Float)] -> [Integer]
lsAdya [] = []
lsAdya ((a,b,w):ys) = aConjunto ([b] ++ lsAdya ys)
-- ¿Está en la adyacencia?
estaEnAdya :: (Integer,Integer,Float) -> [(Integer,Integer,Float)] -> Bool
estaEnAdya (a,b,w) [] = False
estaEnAdya (a,b,w) ys = pertenencia a (lsAdya ys)
-- Cambia las inci
lsInci :: [(Integer,Integer,Float)] -> [Integer]
lsInci [] = []
lsInci ((a,b,w):ys) = aConjunto ([a] ++ lsInci ys)
-- ¿Está en la incidencia?
estaEnInci :: (Integer,Integer,Float) -> [(Integer,Integer,Float)] -> Bool
estaEnInci (a,b,w) [] = False
estaEnInci (a,b,w) ys = pertenencia b (lsInci ys)
--Funcion que pregunta si pertenece el nodo a la grafica
perteneceNodo:: (Integer,Integer,Float) -> [(Integer,Integer,Float)] -> Bool
perteneceNodo elem [] = False
perteneceNodo elem xs = (estaEnInci elem xs) || (estaEnAdya elem xs)


--FUNCION HAMILTONIANA
eshamiltoniana :: Grafica -> Bool
eshamiltoniana ([],ys) = error ("Se ingreso una grafica vacia")
eshamiltoniana (xs,[]) = True
eshamiltoniana (xs,ys) = if esReflexiva (xs,ys)
    then not (masDeUno ys)
    else auxHamil ys
--Auxiliar que revisa si la incidencia existe
auxHamil:: [(Integer,Integer,Float)] -> Bool
auxHamil [] = False
auxHamil (x:xs) =   if xs == []
                    then True
                    else if (devuelveIncidencia x == devuelveNodo(devInciList xs)) == False
                         then False
                         else  auxHamil xs


--FUNCION DOMINIO (de la relación)
dominio:: Grafica -> [Integer]
dominio ([],ys) = []
dominio (xs,[]) = []
dominio (xs,y:ys) = quitarRepetidos((devuelveNodo y):dominio(xs,ys))


--FUNCION IMAGEN : Una función que nos de la imagen de una relación.
imagen:: Grafica -> [Integer]
imagen ([],ys) = []
imagen (xs,[]) = []
imagen (xs,y:ys) = quitarRepetidos((devuelveIncidencia y):imagen(xs,ys))


--FUNCION VERIFICADORA
esFuncion:: Grafica -> Bool
esFuncion ([],ys) = False
esFuncion (xs,[]) = False
esFuncion (xs,ys) = if  (busquedaRepetido(dominioRepetido (xs,ys)) (dominio (xs,ys))) > long( dominio (xs,ys))
                    then False
                    else True


--FUNCION REFLEXIVA : Una función que nos dice si una relación es reflexiva.
esReflexiva::Grafica -> Bool
esReflexiva ([],ys) = False
esReflexiva (xs,[]) = False
esReflexiva (xs,ys) = elementosLista (generaReflex xs) ys


--FUNCION SIMETRICA : Una función que nos dice si una relación es simétrica.
esSimetrica:: Grafica -> Bool
esSimetrica ([],ys) = False
esSimetrica (xs,[]) = False
esSimetrica (xs,ys) =  elementosLista (auxSimetria (xs,ys)) ys
--Funcion Auxiliar que genera la simetría
auxSimetria:: Grafica -> [(Integer,Integer,Float)]
auxSimetria (xs,[]) = []
auxSimetria ([],ys) = []
auxSimetria (xs,y:ys) = [buscaSimetrica y] ++ auxSimetria (xs,ys)
--Funcion Auxiliar que busca la simetría arista por arista
buscaSimetrica:: (Integer,Integer,Float) -> (Integer,Integer,Float)
buscaSimetrica (x,y,z) = (y,x,z)
--Funcion Auxiliar
busquedaEnArista:: [(Integer,Integer,Float)] -> (Integer,Integer,Float) -> Bool
busquedaEnArista [] e = False
busquedaEnArista (x:xs) e = if comparacionSinPeso x e
                         then True
                         else busquedaEnArista xs e
--Funcion Auxiliar Importante universal (Regresa)
elementosLista:: [(Integer,Integer,Float)] -> [(Integer,Integer,Float)] -> Bool
elementosLista [] ys = False
elementosLista xs [] = False
elementosLista (x:xs) (ys) =    if not (busquedaEnArista ys x)
                                then False
                                else if xs == []
                                    then True
                                    else elementosLista xs ys


--Funcion ANTISIMETRICA
esAntisimetrica:: Grafica -> Bool
esAntisimetrica ([],ys) = False
esAntisimetrica (xs,[]) = False
esAntisimetrica (xs,ys) = if esSimetrica (xs,ys)
                          then esReflexiva (xs,ys)
                          else False


--Función COMPOSICIÓN
composicion:: Grafica -> Grafica -> Grafica
composicion xs ([], []) = ([], [])
composicion ([], []) xs  = ([], [])
composicion (xs, ys) (zs, fs) = (quitarRepetidos (devuelveDominio (composLista ys fs)), quitarAristasRepetidos (composLista ys fs))
--Funcion auxiliar que compone arista por arista
compAux:: (Integer,Integer,Float) -> [(Integer,Integer,Float)] -> [(Integer,Integer,Float)]
compAux x [] = []
compAux (w,y,z) (x:xs) = if y == devuelveNodo x
                         then [(w, devuelveIncidencia x ,z + peso x)] ++ compAux (w,y,z) xs
                         else compAux (w,y,z) xs
-- Función Auxiliar que devuelve una lista de aristas
composLista:: [(Integer,Integer,Float)] -> [(Integer,Integer,Float)] -> [(Integer,Integer,Float)]
composLista [] ys = []
composLista xs [] = []
composLista (x:xs) (ys) = compAux x ys ++ composLista xs ys


--Función POTENCIA
potencia:: Grafica -> Integer -> Grafica
potencia ([], []) n = ([], [])
potencia xs 0 = ([], [])
potencia xs 1 = xs
potencia xs n = quitaGraficasRepetidas (composicion xs (potencia xs (n-1)))
--Funcion Auxiliar que quita los repetidos en las graficas en general
quitaGraficasRepetidas:: Grafica -> Grafica
quitaGraficasRepetidas ([],[]) = ([],[])
quitaGraficasRepetidas (xs,[]) = ([],[])
quitaGraficasRepetidas ([],ys) = ([], quitarAristasRepetidas ys)
quitaGraficasRepetidas (xs,ys) = (xs, quitarAristasRepetidas ys)


-- FUNCION CERRADURA REFLEXIVA
cerrReflexiva:: Grafica -> Grafica
cerrReflexiva (xs,ys) = if esReflexiva (xs,ys)
                        then (xs,[])
                        else (xs, quitarElementos (generaReflex xs) ys)


-- Funcion CERRADURA SIMETRICA
cerrSimetrica:: Grafica -> Grafica
cerrSimetrica (xs,ys) = if esSimetrica (xs,ys)
                        then (xs, [])
                        else (xs,quitarElementos (auxSimetria (xs,ys)) ys)


--CERRADURA TRANSITIVA
cerrTransitiva :: Grafica -> Grafica
cerrTransitiva ([],ys) = error ("no hay vertices")
cerrTransitiva (xs,ys) =  (xs, auxiliarCerrTrans [ys])
--Funcion Auxiliar que genera los aristas transitivos
auxiliarCerrTrans :: [[(Integer,Integer,Float)]] -> [(Integer,Integer,Float)]
auxiliarCerrTrans [] = []
auxiliarCerrTrans (y:ys) =  if generadorTransLista y y == []
                            then auxiliarCerrTrans ys
                            else (generadorTransLista y y) ++ auxiliarCerrTrans [y++(generadorTransLista y y)]
--FUNCION AUXILIAR  que dada una arista y una lista de aristas devuelve la lista de aristas transitivas que pueden generar
generadorTrans :: (Integer,Integer,Float) -> [(Integer,Integer,Float)] -> [(Integer,Integer,Float)]
generadorTrans x [] = []
generadorTrans (x,y,z) ((q,w,e):ys) =   if y == q
                                        then [(x,w,z)] ++ generadorTrans (x,y,z) ys
                                        else generadorTrans (x,y,z) ys
--FUNCION AUXILIAR  que dada dos listas de aristas devuelve la lista de aristas transitivas que se pueden generar con esas dos listas dadas
generadorTransLista :: [(Integer,Integer,Float)] -> [(Integer,Integer,Float)] -> [(Integer,Integer,Float)]
generadorTransLista [] xs = []
generadorTransLista xs [] = []
generadorTransLista (x:xs) ys = quitarElementos(quitarAristasRepetidas(generadorTrans x ys ++ generadorTransLista xs ys)) ys
