-- Recibe una cadena y el largo de la cadena
 -- Te da el indice de cada caracter en la cadena
enBolsa :: [a] -> Int -> [(a,Int)]
enBolsa [] a = error "Algo salió mal al medir la cadena"
enBolsa xs 0 = []
enBolsa xs a = enBolsa xs (a-1) ++ [(charAt (a-1) xs,a)]
-- CharAT - Recibe un entero y una lista (o cadena)
			-- Nos regresa el caracter que resida en el indice recibido
charAt:: Int -> [a] -> a
charAt 0 (x:xs) = x
charAt n (x:xs)= if n < 0 || n > tamanioLista (x:xs)
	              then error "No estes molestando"
					  else charAt (n-1) xs
charAt 0 [] = error "Mensaje de error"
-- Te da el tamaño de una lista recibida
tamanioLista:: [a] -> Int
tamanioLista [] = 0
tamanioLista (x:xs) = 1 + tamanioLista xs
