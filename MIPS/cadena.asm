.data
str1:	.asciiz "Hola Mundo!"
str2:	.space	20
x:	.word	400

.text
	la	$t0 str1	#cargar la direccion de la cadena
	la	$t1 str2	#cargar la direccion del buffer
ini:	lb	$a0 ($t0)	#cargamos el simbolo de la cadena
	beq	$a0 '\0' fin	#verificar si ese simbolo no es fin de cadena, si es entonces salta al fin
	sb	$a0 ($t1)	#guardar el simbolo en el buffer(copiar)
	addi	$t0 $t0 1	#pasar a la direcci??n del siguiente simbolo
	addi	$t1 $t1 1	#pasar a la direccion donde pegara el siguiente simbolo
	j	ini		#salto para repetir el ciclo
fin:	li	$a1 '\0'	#poner fin de cadena a la copia
	sb	$a1 ($t1)