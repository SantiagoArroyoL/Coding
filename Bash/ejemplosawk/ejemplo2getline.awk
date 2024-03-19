BEGIN{
	print "Dame tu nombre"
	getline < "/dev/tty"
	print $0
}
