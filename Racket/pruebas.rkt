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
(car lista1) ;; 1

;; contents of the decrement register
(cdr lista1) ;; Todo menos 1 de la lista

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


;; Función que dada una lista, multiplica todos los elementos contenidos en la misma. USANDO LAMBDA
(define (multiplicar lst)
  (foldl (lambda (number)
              (* number number)) 1 lst))

(multiplicaDos '(1 2 3))
(multiplicar '(1 2 3))
