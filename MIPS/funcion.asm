.data

.text
	main:
		#Guardamos 50 en a1 con add inmediate
		addi $a1, $zero, 50
		addi $a2, $zero, 100
		
		#LLamamos a la funcion
		jal suma 
		
		# Imprimimos pa ver si lo hizo
		li $v0, 1
		addi $a0, $v1, 0
		syscall 
		
	#Le decimos al sistema que el programa termino
	li $v0, 10
	syscall
	
	suma:
		add $v1, $a1, $a2
		
		jr $ra