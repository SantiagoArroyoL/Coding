	.text
	div $t0 , $t0 , $t0
	li $t0 , 0x7FFFFFFF
	addi $t0 , $t0 , 1

	.kdata

error: .asciiz "Ocurrio un error"
	.ktext 0X80000180
	
	mfc0 $k0, $13 #Copy $13 (cause) from coprocessor 0 to $k0.
	andi $k0, $k0, 0x7C
	beq $k0, 0x30, over
	li $v0, 10
	syscall
over:
	la $a0, error
	li $v0, 4
	syscall
