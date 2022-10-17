#lang racket
#|Integrantes:
   Santiago Arroyo Lozano
|#


;; Q1 La istancia de Hamming
;; hamming: l1,l2 -> int
;; calculamos la distancia de hamming
(define (hamming l1 l2) 
  (let*  ([c1 (checa l1)]
         [c2 (checa l2)]
         [n (string-length c1)])
    (if (eq? n (string-length c2))
        (hammingAux c1 c2 (sub1 n))
        (error "Por favor introduce cadenas de la misma longitud"))))
;; LLamada recursiva
(define (hammingAux c1 c2 n)
  (cond
    [(> 0 n) 0]
    [(eq? (string-ref c1 n) (string-ref c2 n))
     (hammingAux c1 c2 (sub1 n))]
    [else (add1 (hammingAux c1 c2 (sub1 n)))]
    ))
;; checa: c -> string
;; Revisamos si c es una cadena y si no lo es la convertimos
(define (checa c) (if (string? c) c (~v c)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Q2. Sucesión fractal
;; Función que recibe un entero positivo y regresa los primeros n elementos de la sucesión
;; fractal: int -> listof number
(define (fractal n) (map fractal-aux (build-list n values)))
;; Función auxiliar que revisa cada término
;; Si el termino es par lo dejamos como tal, si no llamamos recursivamente
;; fractal-aux: int -> int
(define (fractal-aux n)
  (cond
    [(zero? n) 0]
    [(= 1 n) 0]
    [(zero? (modulo n 2)) (floor (/ n 2))]
    [else (fractal-aux (floor (/ n 2)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Q3. Anagrama
;; anagramas-de: (string, list) -> list
;; Filtraremos todos los no anagramas de la lista
(define (anagramas-de c l)
  (filter (lambda (x) (anagrama c x)) l))
;; anagrama: (string, string) -> bool
;; Ordenamos las cadenas para comparar dos cadenas ordenadas
;; Y así poder revisar si son anagramas o no
;; Para poder ordenar las transformamos a lista y luego de regreso
(define (anagrama c1 c2)
  (let* ([l1 (list->string (sort (string->list c1) char<?))]
        [l2 (list->string (sort (string->list c2) char<?))])
  (equal? l1 l2)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Q4 A. div-tree
;; Primero definimos la estructura leaf y node (tree)
(define-struct leaf (number?) #:transparent)
(define-struct node (v i d) #:transparent)
;; div-tree: int -> node
(define (div-tree n) (div-treeAux n (prime-fac n)))
;; La llamada recursiva recibe el cociente en el que vamos que será el nodo y la lsta de divisores que serán las hojas
;; div-treeAux: int -> node
(define (div-treeAux n divisores)
  (cond
    [(empty? (rest divisores)) (leaf (first divisores))]
    [else (node n (leaf (first divisores)) (div-treeAux (quotient n (first divisores)) (rest divisores)))]))


;; Q4 B. prime-fac
;; Función que toma un número y regresa una lista con la
;; descomposición en factores primos del mismo.
;; descomposicion-primos : number -> (listof number)
(define (prime-fac n)
  (let ([l (criba-eratostenes n)]) (primos n l)))
;;LLamada recursiva
(define (primos n l)
  (cond
      [(= n 1) '()]
      [(zero? n) '()]
      [(zero? (modulo n (first l)))
       (append (list (first l)) (primos (quotient n (first l)) l))]
      [else (primos n (rest l))]))
;; Función que encuenta los números primos en un rango de 2 a n
;; usando la Criba de Eratóstenes.
;; criba-eratostenes : number → (listof number)
(define (criba-eratostenes n)
   (letrec ([no-divides? (lambda (x xs) (filter (lambda (a) (or (< a x) (not (= (modulo a x) 0)))) (if (empty? xs) '() (rest xs))))] 
            [criba-rec (lambda (xs) (cond
                                      [(empty? xs) xs]
                                      [else (cons (first xs) (criba-rec (no-divides? (first xs) xs)))]))])
     (cond
        [(= n 1) error "Por favor introduce un número mayor a 2"]
        [else (criba-rec (range 2 (+ 1 n)))] 
   )))
;; Tal cual una función que te dice si divide o no
[define no-divides? (lambda (x xs) (filter (lambda (a) (or (< a x) (not (= (modulo a x) 0)))) (if (empty? xs) '() (rest xs))))] 


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; PUNTOS EXTRA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (my-length lst)
 (cond
  [(empty? lst) 0]
  [else (+ 1 (my-length (rest lst)))]))


