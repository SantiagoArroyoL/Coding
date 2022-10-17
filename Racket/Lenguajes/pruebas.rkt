#lang plai
;; Dialecto: Variación del lenguaje
;; plai: Programming Languages Application and Interpretation (Libro)

(let ([a 2] [b 3] [c 4])
  (+ a b c)) ;;9

(let ([a 2])
  (let ([b (+ a a)])
    (+ a b))) ;; 6

;; let* es azúcar sintáctica de lets anidados
;; let -> with
;; let* -> with*
(let* ([a 2] [b (+ a a)])
  (+ a b)) ;; 6

(let* ([a 2] [b a] [c b] [d c])
  (+ a b c d)) ;; 8

(if (> 10 2)
    3
    (if (> 4 2)
        4
        (if (> 50 30)
            1
            4))) ;; 3

;; Condicionales, es como un switch
(cond
   [(> 10 2) 3]
   [(> 4 2) 4]
   [(> 50 30) 1]
   [else 4])  ;; 3

;; quote se lee como: TÓMALO LITERAL, NO LO INTERPRETES
(quote (1 2 3))

(define lista1 '(1 2 3 4 5 6 7 8 9 10))

;; contents of the address register
(car lista1) ;; cabeza de la lista

;; contents of the decrement register
(cdr lista1) ;; cola de la lista

(first lista1) ;; car

(rest lista1)  ;; cdr

(cadr lista1) ;; car+1

(caddr lista1) ;; car+2

(empty? lista1) 

(null? lista1)

;; Función que suma los elementos de la lista
(define (sumal l)
  (if (empty? l)
      0
      (+ (car l) (sumal (cdr l)))))

(sumal '(1 2 3))

;; Función que multiplicada todos los elementos de una lista por 2 USANDO MAP y LAMBDA
(define (multiplicaDos lst)
  (map (lambda (number) (* 2 number)) lst))


;; Función que dada una lista, multiplica todos los elementos contenidos en la misma.
(define (multiplicar lst)
  (if (empty? lst)
      1
      (* (first lst)
         (multiplicar (rest lst)))))

(multiplicaDos '(1 2 3))
(multiplicar '(1 2 3))

;; Practica1 - Arroyo Lozano Santiago
;; 317150700

;; 1. Predicado que nos dice si un numero es negativo
;; neg?: number -> Boolean
(define (neg? a)
  (if (> a 0)
    #f
       #t))

(neg? -3)

;; 2. Predicado que nos dice si un numero es par
;; esPar?: numner -> boolean
(define (esPar? n)
  (if (= (modulo n 2) 0)
    #t
       #f))

(esPar? -2)

(esPar? 0)

;; 3. Procedimiento que nos devuelve el valor absoluto de un número
;; absoluto: number -> number
(define (absoluto n)
  (if (< n 0)
    (* n -1)
       n))

(absoluto -5)

;; 4. Procedimiento que calcula el area de un cono de base circular
;; area-cono: number number -> number
(define (area-cono d g)
  (define r (/ d 2))
  (+ (* (* pi r) g)(* (expt r 2) pi)))

(area-cono 10 15)

;; 5. Procedimiento que eleva el numero a, a la potencia b
;; potencia: number number
(define (potencia a b)
  2)

(potencia 2 -3)

;;estructuras heterogeneas
(define (any? a)
  #t)
;;Definimos el tipo de dato Arbol
(define-type Arbol
  [hoja (elem any?)]
  [nodo (elem any?) (izq Arbol?) (der Arbol?)])

;;Función numero-hojas usando type-case
;;(numero-hojas1 (nodo 2 (hoja 3) (hoja 1))) = 2
;;numero-hojas1: Arbol -> numero
(define (numero-hojas1 a)
  (type-case Arbol a
    [hoja (x) 1]
    [nodo (x i d) (+ (numero-hojas1 i) (numero-hojas1 d))]))

;;Función numero-hojas usando match
;;(numero-hojas2 (nodo 2 (hoja 3) (hoja 1))) = 2
;;numero-hojas2: Arbol -> numero
(define (numero-hojas2 a)
  (match a
    [(hoja x) 1]
    [(nodo x i d) (+ (numero-hojas2 i) (numero-hojas2 d))]))

;;Función que aplana un árbol binario con type-case, pre-orden
;;(aplana1 (nodo 2 (hoja 3) (hoja 1))) = '(2 3 1)
;;aplana1: Arbol -> (listof any)
(define (aplana1 a)
  (type-case Arbol a
    [hoja (x) (list x)]
    [nodo (x i d) (append (list x) (aplana1 i) (aplana1 d))]))


;;Función que aplana un árbol binario con match, pre-orden
;;(aplana2 (nodo 2 (hoja 3) (hoja 1))) = '(2 3 1)
;;aplana2: Arbol -> (listof any)
(define (aplana2 a)
  (match a
    [(hoja x) (list x)]
    [(nodo x i d) (append (list x) (aplana2 i) (aplana2 d))]))