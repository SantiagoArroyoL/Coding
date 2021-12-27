.data
	uno: .float 1.0
	cuatro: .float 4.0
	tres: .float 3.0
	n: .float 0.0
	m: .float 5.0
.text
	main:
		lwc1 $f1 uno
		lwc1 $f2 n
		lwc1 $f3 m
		lwc1 $f4 cuatro
		lwc1 $f7 tres
	
	suma: c.le.s $f2, $f3
		bc1f end
		
		#Lado izquierdo
		mul.s $f5, $f4, $f2
		add.s $f5, $f1, $f5
		div.s $f5, $f1, $f5
		
		#Lado derecho
		mul.s $f0, $f4, $f2
		add.s $f0, $f1, $f0
		div.s $f0, $f7, $f5 
		
		sub.s $f6, $f5, $f0
	
	end: mul.s $f12, $f4, $f6
		li $v0, 3
		syscall