BEGIN{
	print "Dame el primer numero"
	getline num1 < "/dev/tty"
	print "Dame el segundo numero"
	getline num2 < "/dev/tty"
	print "Dame el operador"
	getline opera < "/dev/tty"
	if (opera=="+")
		resultado=suma(num1,num2)
	if (opera=="-")
		resultado=resta(num1,num2)
	if (opera=="*")
		resultado=multiplica(num1,num2)
	if (opera=="/")
		resultado=divide(num1,num2)
	print "El resultado es:", resultado
}
