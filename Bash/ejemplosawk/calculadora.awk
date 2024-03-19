BEGIN{
	print "Dame el primer numero"
	getline num1 < "/dev/tty"
	print "Dame el segundo numero"
	getline num2 < "/dev/tty"
	print "Dame la operacion"
	getline operador < "/dev/tty"

	if(operador=="+"){
		resultado=num1+num2
	}
	if(operador=="-"){
		resultado=num1-num2
	}
	if(operador=="*"){
		resultado=num1*num2
	}
	if(operador=="/"){
		resultado=num1/num2
	}
	print "El resultado es:", resultado
}
