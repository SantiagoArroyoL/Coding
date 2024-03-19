BEGIN{
	romanos="I,II,III,IV,V,VI,VII,VIII,IX,X"
	split(romanos,numeros,",")
}
$1>0 && $1<10{
	print numeros[$1]
}
