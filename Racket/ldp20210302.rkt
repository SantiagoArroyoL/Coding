#lang plai

;; Dialecto: Variación del lenguaje
;; plai: Programming Languages Application and Interpretation (Libro)

;; 1. Establecer su nombre
;; 2. Escribir un comentario que nos qué hace
;; 3. Definir su firma (comentarios)
;; 4. Escribir pruebas
;; 5. Implementarla

;; LOS TIPOS BÁSICOS NO LLEVAN PARÉNTESIS: números, booleanos, las cadenas, los símbolos, 
;; los caracteres.

;; Función que calcula el promedio de tres números.
;; promedio: number number number -> number
(define (promedio a b c)
  (/ (+ a b c) 3))

(test (promedio 10 10 10) 10)
(test (promedio 10 4 4) 6)
(test (promedio 9 8 10) 9)

(promedio 10 10 10)

;; Condicionales
;; if condición, bloque de código
;; if (10 > 20)
;;     printf("Entré al if");
;; PROBLEMA DEL ELSE SUELTO
;; Punto Extra (+0.5 sobre Tarea 1): Investigar en qué consiste el problema del else-suelto y 
;; dar un ejemplo.
;; 9 de marzo (manu@ciencias.unam.mx)
;; INDIVIDUAL

;; Todas las expresiones deben regresar un valor.
;; (if codicion then else)

;; Función que calcula el valor absoluto.
;; absoluto: number -> number
(define (absoluto x)
  (if (>= x 0)
      x
      (* x -1)))

(test (absoluto -1) 1)
(test (absoluto 10) 10)
(test (absoluto -18) 18)


;; (if condicion then else)
;; condicion (>= x 0)
;; then x
;; else (* x -1)

;; cond
;;(cond
;;   [condicion1 valor1]
;;   [condicion2 valor2]
;;   ...
;;   [else valor-else])

;; Función que dado un número (1-12) nos regresa
;; el mes que representa.
;; mes: number -> string
(define (mes n)
  (cond
     [(= n 1) "Enero"]
     [(= n 2) "Febrero"]
     [(= n 3) "Marzo"]
     [else (error 'mes "Mes fuera de rango")])) ;; opcional

(test (mes 1) "Enero")
(test (mes 2) "Febrero")
(test (mes 3) "Marzo")
(test/exn (mes 14) "Mes fuera de rango")

(mes 14)


