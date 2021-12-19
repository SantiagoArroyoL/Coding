.data
x:	.float 1.1 #NO es posible operar con inmediatos,
			   # por lo que se deben declarar aqui y cargarlos
z:	.float 0.0
y:	.float 5.3

.text
	lwc1	$f1 x
	lwc1	$f2 y
	lwc1	$f3 z
	lwc1	$f4 x
while:	c.le.s  $f1 $f2	#aqui se hace la comparacion de $f1 y $f2
						# y se guarda el valor de verdad del resultado
	bc1f	end	#aqui si el valor de verdad de esa comparacion
				# es falso se salta
	add.s	$f3 $f3 $f1
	add.s	$f1 $f1 $f4
	j	while
	
end: 