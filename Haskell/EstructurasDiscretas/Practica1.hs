{-
Programador: Arroyo Lozano Santiago
Materia: Estructuras Discretas
Fecha de entrega: 16/Agosto/2019
-}

--Función suma
suma::Int->Int->Int
suma a b = a + b

--Función resta
resta::Int->Int->Int
resta a b = a - b

--Función multiplicación
multi::Float->Float->Float
multi a b = a * b

--Función división
divis::Float->Float->Float
divis a b = a / b

--Comparador
comp::Float->Float->Int
comp a b = if a == b
			  then 0
			  else
			  if a>b
			  then 1
			  else -1

--Función Potencia
pow a b = a ^ b

--Máximo entre tres número
maximo:: Float->Float->Float->Float
maximo a b c = if a>b
	then if a>c
	     then a
		  else c
	else if b>c
		  then b
		  else c

--Distancia entre dos puntos
distanciaPuntos::Float->Float->Float->Float->Float
distanciaPuntos x1 x2 y1 y2 = sqrt((x2 - x1)^2 + (x2 - x1)^2)

--Hipotenusa de un triangulo rectángulo
hipotenusa::Float->Float->Float
hipotenusa b h = sqrt(b^2 + h^2)

--Pendiente de la recta que pasa por dos puntos.
pendiente::Float->Float->Float->Float->Float
pendiente x1 x2 y1 y2 = (y1 - y2) / (x1 - x2)

--Raices de una ecuación cuadrática
raices::Float->Float->Float->(Float, Float)
raices a b c = if d < 0
	then error "Raíz imaginaria"
	else (x1, x2)
	where
		x1 = e + sqrt d /(2*a)
		x2 = e - sqrt d /(2*a)
		d = b * b - 4*a*c
		e = - b / (2*a)

-- Volumen de una piramide regular
volPir::Float->Float->Float->Float
volPir l h n = (l*h*n)/3
