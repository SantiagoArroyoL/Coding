.data
	arreglo: .word 14, 12, 13, 5, 9, 11, 3, 6, 7, 10, 2, 4, 8, 1
.text

main:       
	la  $t0, arreglo     # Direccionamos el arreglo a $t0
	add $t0, $t0 40
outterLoop:
	add $t1, $zero, $zero
	la $a0, arreglo      # Direccionamos el arreglo a $a0
continue:
	addi $a0, $a0, 4
	bne $a0, $t0, innerLoop
	bne $t1, $zero, outterLoop
innerLoop:
	lw  $t0, 0($a0)      # decimos que $t0 sea elelemento actual en el arreglo
    lw  $t1, 4($a0)      # sea $t1 el siguiente elemento en el arreglo
    slt $t5, $t2, $t3    # $t5 = 1 si $t0 < $t1
	beq $t5, $zero, continue #(intercambiamos)
	addi $t1, $zero, 1
	sw  $t0, 4($a0)      # guardamos los elementos grandes en la parte high del arreglo
    sw  $t1, 0($a0)      # guardamos los elementos pequeños en la parte low del arreglo