.data
	mensajeX: .asciiz "Digita el valor de x: "
	mensajeN: .asciiz "Digita el valor de n: "
	r: .float 1.0
	dos: .float 2.0
	uno: .float 1.0
	zeroF: .float 0.0
.text
	main:
		#Mostramos mensaje x
		li $v0, 4
		la $a0, mensajeX
		syscall
		#Leemos x en $f0
		li $v0, 6
		syscall
		#Movemos valor x
		mov.s $f1, $f0
		
		#Mostramos mensaje x
		li $v0, 4
		la $a0, mensajeN
		syscall
		#Leemos y en $f0
		li $v0, 6
		syscall
		#Movemos valor n
		mov.s $f2, $f0
		
		lwc1 $f7 zeroF
		lwc1 $f3 r
		add.s $f4, $f7, $f1 #y 
		lwc1 $f5 dos
		lwc1 $f6 uno
	
	while: c.le.s $f6, $f2
		bc1f end

    	div.s $f0, $f2, $f5   # Dividimos n entre 2
    	floor.w.s  $f8, $f0   # Truncamos para obtener el numero sin resiudo
		cvt.d.w $f8, $f8

		sub.d $f0, $f0, $f8   # Restamos para obtener el resiudo
		c.eq.s $f6, $f0       # comparamos con 1
		
		bc1t then
		
		div.s $f2, $f2, $f5   # n = n/2
		mul.s $f4, $f4, $f4   # y = y*y
	
	then:
		mul.s $f3 $f3, $f4    # r = r*y
		
	end:
		#Imprime r
		li $v0, 3
		mov.s $f12, $f3       #Solo $f12 se imprime asi que lo movemos
		syscall
	
		
