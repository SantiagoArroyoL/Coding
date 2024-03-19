while true; do
	if [ -z "$1" -o -z "$2" ]; then
		echo -n "Ingresa el primer número: "
		read n1
		echo -n "Ingresa el segundo número: "
		read n2
	else
		n1=$1
       		n2=$2	
	fi
	#Regex pa verificar que sean números, incluso flotantes y evitar errores
	if [[ ! $n1 =~ ^-?[0-9]+([.][0-9]+)?$ ]] || [[ ! $n2 =~ ^-?[0-9]+([.][0-9]+)?$ ]]; then
		echo "Error! Ambos valores deben ser números."
		exit 1
	fi

	echo "*****************************************"
	echo ""
	echo "* Bienvenido a la calculadora, $USER !*"
	echo ""
	echo "*****************************************"
	echo ""
	echo ""
	echo "Seleccione una operación:"
	echo "1.- Suma"
	echo "2.- Resta"
	echo "3.- Multiplicación"
	echo "4.- División"
	echo "5.- Módulo"
	echo "6.- Salir"
	read opcion

	case $opcion in
	    1) result=$((n1+n2))
		echo "Resultado: $result"
		;;
	    2) result=$((n1-n2))
	        echo "Resultado: $result"
	        ;;
	    3) result=$((n1*n2))
	        echo "Resultado: $result"
	        ;;
	    4) if [ "$n2" -eq "0" ]; then
	           echo "Error: División por cero."
	       else
		   result=$((n1 / n2))
	           echo "Resultado: $result"
	       fi
	       ;;
	    5) if [ "$n2" -eq "0" ]; then
	           echo "Error: Módulo por cero."
	       else
		   result=$((n1 % n2))
	           echo "Resultado: $result"
	       fi
	       ;;
	    6) echo "Saliendo..."
	       exit 0
	       ;;
	    *) echo "Operación desconocida."
	       ;;
	esac
	
	echo -n "¿Deseas realizar otra operación? (s/n): "
	read respuesta
	if [[ $respuesta != "s" ]]; then
		echo "Saliendo..."
	        exit 0
	fi
done
