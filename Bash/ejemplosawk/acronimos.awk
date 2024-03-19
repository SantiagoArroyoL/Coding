BEGIN{
	FS="="
}
FILENAME=="acronimos.txt"{
	acro[$1]=$2
}
FILENAME!="acronimos.txt" && FNR==1{
	FS=" "
}
FILENAME!="acronimos.txt"{
	for (i=1;i<=NF;i++)
	{
	if ($i in acro)
		printf "%s ", acro[$i]
	else
		printf "%s ", $i
	}
	printf "\n"
}
