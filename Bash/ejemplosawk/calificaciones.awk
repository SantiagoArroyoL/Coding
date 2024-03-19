BEGIN {
    FS = " "
}
{
    nombre = $1
    for (i = 2; i <= NF; i++) {
        calificaciones[nombre][i - 1] = $i
    }
}
END {
    for (nombre_estudiante in calificaciones) {
        suma = 0
        num_calificaciones = length(calificaciones[nombre_estudiante])
        
        for (i = 1; i <= num_calificaciones; i++) {
            suma += calificaciones[nombre_estudiante][i]
        }
        promedio = suma / num_calificaciones
        print "Estudiante:", nombre_estudiante, "Promedio:", promedio
    }
}
