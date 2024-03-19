BEGIN{
	print "Dame el nombre del usuario"
	getline nombre < "/dev/tty"
}
{
	if ($1==nombre){
	cuenta_sesiones++
}
}
END{
	if (cuenta_sesiones>0)
		print "El usuario si esta"
	else
		print "El usuario no esta"
}
