#!/bin/bash
# https://linuxopsys.com/topics/pass-all-arguments-in-bash#:~:text=is%204%207.-,The%20%24*%20variable,IFS%20(internal%20file%20separator).

str="$*"

n=${#str}

rts=""

for (( i=$n; i>0; i-- )); do
    char=$(echo -n $str | cut -c $i)
    rts="$rts$char"
done

echo $rts
