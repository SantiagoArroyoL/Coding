BEGIN{
	"date" | getline
	print "La fecha de hoy es: " $0
}
