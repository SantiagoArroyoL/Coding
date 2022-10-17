#|
Compiladores 2023-1
Profesora: Dra. Lourdes del Carmen Gonzalez Huesca
Ayudante: Ayud. Braulio Aaron Santiago Carrillo
Laboratorio: Juan Alfonso Garduño Solís

Introduccion a Racket
Nota aclaratoria: No estoy usando acentos a proposito. Algunos editores pueden tener
problemas entre los distintos tipos de codificacion.

Cuando instalen racket se van a instalar 3 cosas:
 racket  - Compilador, interprete y run-time system.
 DrRacket- Ambiante para programar.
 raco    - La herramienta de linea de comando para instalar 
           librerías.

Al inicio de un rachivo rkt se debe colocar el lenguaje con el que vamos a trabajar,
algunos ejemplos son:

 typed/racket   Sistema de tipos estático.
 lazy           Racket perezoso.
 frtime         Para trabajr con programación reactiva.
 scribble/base  Un tipo de latex, done el código de 
                igual manera se renderiza, sirve para 
                documentar.

Con raco podemos generar ejecutables de nuestros programas con el siguiente comando:
 > raco exe file.rkt
|#

#lang racket

;Tenemos dos tipos principales de definiciones:
;(define <id> <expr>)
(define año 2023)

;(define (<id> <id's>*) <expr>+)
(define (suma10 n)
        (+ n 10))


;Estructuras de control: 
;if:  (if <expr> <expr> <expr>)
;En racket expresion siempre va a ser evaluada y dependiendo de su resultado 
;se evalúa la primera o la segunda de manera que podemos hacer cosas como 
(if #t (+ 1 1) (/ 0 0))
;sin temor a que se queje el interprete o compilador.

;La siguiente estructura es el cond, que es equivalente al switch de otros 
;lenguajes de programacion:
 ;(cond cond-clause ...)
 ;cond-clause   =   [test-expr then-body ...+]
 ;    |   [else then-body ...+]
 ;    |   [test-expr => proc-expr]
 ;    |   [test-expr]
;Ejemplo:
(define (condicional n)
  (cond
    [(eq? n 1)
     "uno"]
    [(eq? n 2)
     "dos"]
    [(eq? n 3)
     "tres"]
    [else "nose"]))

;Para trabjar con valores booleanos tenemos las siguientes funciones básicas
;(or <expr>*)
;(and <expr>*)
;(not <expr>)

;Se evalúan por necesidad

; (or e1 e2
;     (if (eval e1) #t (eval e2)))

; (and e1 e2
;     (if (eval e1) (eval e2) #f))


;Racket es permisivo y nos deja ahcer cosas como esta:
(define (double v)
  ((if (string? v) string-append +) v v))

;Y tambien podemos hacer lo siguiente:
(define (dosVeces f v) 
    (f (f v)))
;Esto es una funcion de orden superior, así que tambien podemos tener funciones
;anónimas. (lambda (‹id›*) ‹definition›* ‹expr›+)
;Ejemplo:

(dosVeces (lambda (n) (+ 10 n)) 7)

(define (zzuma n2)
  (lambda (s) (+ s n2)))

;Alcances, podemos definir funciones dentro del cuerpo de una definicion y 
;utilizarla dentro de ella. Osease (define (<id> <id>*) <defintion>* <expr>*)

(define (ejemploDef n)
  (define (mayorQue10 n2)
        (> n2 10))
  (define si "Sí")
  (cond
   [(mayorQue10 n)
        si]
   [else
        "No"]
   ))

;Let y let*: local binding
;(let ({[ ‹id› ‹expr› ]}* ) ‹expr›+)
;Cada uno de estos id's está ligado al resultado de su 
;respectiva expr, y el alcance que tienen es el cuerpo del let
;es decir, las expresiones de afuera.

(define experimento
(let ([a (random 4)]
      [b (random 4)])
    (cond
     [(> a 4) "Alice gana"]
     [(> b 4) "Bob gana"]
     [else "Empate"])))



;La forma let*, por el contrario, permite 
;que las cláusulas posteriores utilicen enlaces anteriores:
(define experimento2
(let* ([a 10]
      [b 20]
      [x (random b)])
    (cond
     [(> a x) "Alice gana"]
     [(> b x) "B gana"]
     [else "Error"])))

;Listas
;La construcción de una lista tiene la siguiente sintaxis
;(list <elems>*), por ejemplo: ;(define mylist (list 1 2 3 4 5))
;Y no son homogeneas,
;tenemos las funciones clásicas: length, list-ref, append, reverse, member
; take, drop etc.
;Y, como ya quedamos que racket soporta funciones de 
;orden superior, tenemos los tipicos iteradores como map, andmap y ormap.
;Y claro que recursion, definimos el ejercicio clasico de 
;recursion, longitud de una lista

(define (longitud lst)
 (cond
  [(empty? lst) 0]
  [else (+ 1 (longitud (rest lst)))]))

;Ya como último para definir nuestras estructuras utilizamos define-struct,
;para definir listas hacemos los siguiente:

(define-struct emptyL () #:transparent)
(define-struct consL (x y) #:transparent)

; Un ejemplo de map para nuestras listas
(define (my-map f l)
  (match l
    [(emptyL) l]
    [(consL a l2) (consL (f a) (my-map f l2))]))

;; Lista de 256 ceros
(define ceros ((build-list 256 (lambda (x) (* 0 x)))))

;;char a integer respecto a su unicode. (Dado un indice de char en una cadena)
(define (ord c n)
   (char->integer (string-ref c n)))