BEGIN{
	romanos="I,II,III,IV,V,VI,VII,VIII,IX,X"
	split(romanos,numeros,",")
	for ( i in numeros)
		print numeros[i]
}
