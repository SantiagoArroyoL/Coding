.data 
	myMessage: .asciiz "Hello World \n"
.text
	li $v0, 4 #Imprime
	la $a0, myMessage
	syscall
