$0 ~ /pera/ {
	getline
}
{
	print "Num Linea", NR
	print "Linea", $0
}
