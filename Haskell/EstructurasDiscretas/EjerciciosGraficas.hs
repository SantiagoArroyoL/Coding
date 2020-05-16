{-
Grafica

o ------- o   G
|         |
|         |
o ------- o

             w_3
     o ----------- o
     |       e_3  /
w_1  | e_1       /
     |      e_2 / w_2
     |         /
     | e_4    /
     o ----- o
        w_4

... y demás ejemplos que no puedo escribir

conexiones entre vertices (v) y aristas (a1, a2, ... , e1, e2) e = edge
w = weight, peso o costo del trayecto

G = (V, E)
V = { v_1, ..., v_n}
E = { e_1, ..., e_k}
e_i = (v_j, v_z)      i = {1, ..., k}
E contenido VxV

Ingrado = vertices que entran
Exgrado = vertices que salen
Grado = suma de ingrado y exgrado
         e_i = (v_j, v_k)
Camino = e_i+1 = (v_k, v_z)
Gráfica Hamiltoniano =  se puede llegar a todos los vertices

-}
-- G = (V, E) = ([1, 2, 3, 4], [(1, 1, w_6), (2, 3, w_5), ...])
type Grafica = ([Integer],[(Integer,Integer,Float)])

muestra:: Grafica -> Grafica
muestra xs = xs

--Funcion auxiliar busquedaLista
busquedaLista:: Eq a => [a] -> a -> Bool
busquedaLista [] e = False
busquedaLista (x:xs) e = if x == e
	then True
	else busquedaLista xs e

-- Incidencias devuelve los vertices que tengan como segunda entrada al primero
incidencias :: Grafica -> Integer -> [Integer]
incidencias (xs, []) n = []
incidencias (xs, ((a, b, w):ys)) n = if b == n
                                     then [a] ++ incidencias (xs,ys) n
                                     else incidencias (xs,ys) n
-- incidencias (xs , ((a, b, _):ys)) x zs = if busquedaLista x zs
--                                         then [zs ++ [x]]
--                               else superCaminos (xs,(a, b, _):ys) (zs ++ [x]) (adyacencias (xs,(a, b, ):ys) x)
{-
incidencia ([1, 2, 3], [(1, 3, 6),(1, 2, 4),(2, 3, 7)]) 1
incidencia ([1, 2, 3], [(1, 2, 4),(2, 3, 7)]) 1             [3,]
incidencia ([1, 2, 3], [(2, 3, 7)]) 1                       [3,2,]
incidencia ([1, 2, 3], []) 1                                [3,2,]
                                                            [3,2,[]]
-}

longitud :: [Integer] -> Integer
longitud [] = 0
longitud (x:xs) = 1  + longitud xs

-- ingrado :: Grafica -> Integer -> Integer
-- ingrado g n = longitud (incidencias g n)

-- esHamiltoniana :: Grafica -> Bool
-- esHamiltoniana g =

-- caminos :: Grafica -> Integer -> [Integer] -> [[Integer]]
-- (xs, []) n =


-- adyacencias :: Grafica -> Integer -> [Integer]
-- adyacencias g n =

-- superCaminos :: Grafica -> Integer -> [Integer] -> [Integer]
-- superCaminos g xs (a:as) = (caminos g a xs) ++ (superCaminos a xs as)
-- xs = [1, 3, 5, 6, 2]
-- (a:as) = [1, 2]
