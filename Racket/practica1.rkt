#lang plai
;; FUNCIONES AUXILIARES
(define (digitos n)
    (+ 1 (floor (/ (log n) (log 10))))
)

(define (a-lista n . args)
  (let ((b (if (null? args) 10 (car args))))
    (let loop ((n n) (d '()))
      (if (zero? n) d
          (loop (quotient n b)
                (cons (modulo n b) d))))))

;;Función que dados el largo, ancho y altura de un paralelepípedo
;;rectángulo respectivamente, calcula el área lateral del mismo.
;;area-lateral : number number number -> number
(define (area-lateral a b c) (* 2 (+ a b) c))

;;Función ue dada la generatriz, la altura y el diámetro de la base
;;de un cono circular recto, calcula el área total del mismo.
;;area-total : number number -> number
(define (area-total g d) (let ([r (/ d 2)])
                           (+ (* pi r g) (* pi r r))))

;;Función que dados cuatro números indica si se encuentran ordenados
;;de forma decremental.
;;decremental ?: number number number number -> boolean
(define (decremental? a b c d)
  (and (> a b) (and (> b c) (> c d))))

;;Función que dado un número que representa el número de escalones
;;de una escalera, nos indica el número de formas en que se puede
;;subir saltando, en cada salto se puede subir 1, 2 o 3 escalones
;;tomando en cuenta que hay cuatro formas dinstintas de subir:
;;1, 1, 1; 1, 2; 2, 1 o 3.
;;numero-formas : number -> number
(define (numero-formas e)
   (cond
     [(= e 0) 0]
     [(= e 1) 1]
     [(= e 2) 2]
     [(= e 3) 4]
     [else (+ (numero-formas (- e 1)) (numero-formas (- e 2)) (numero-formas (- e 3)))]
   ))

;;Función que dado un número natural, indica si es raro.Un número natural
;;es raro si al sumar cada una de sus cifras elevadas al número de cifras
;;que lo forman, se obtiene el propio número.
;; raro ?: number → boolean
(define (raro? n )
  (let ([lst (map (lambda (number) (expt number (digitos n))) (a-lista n))])
    (= (apply + lst) n)))

;;Función que dado un número, construya una cadena que dibuje un
;;rombo con dicho número de dígitos.
;;rombo : number -> string
(define (rombo n)
  (cond
   [(= n 1) "0\n0\n0"] 
   [(= n 2) " 0\n101\n 0"]
   [(= n 3) "  0\n 101\n21012\n 101\n  0"]
   [(= n 4) "   0\n  101\n 21012\n3210123\n 21012\n  101\n   0"]
   [(= n 5) "    0\n   101\n  21012\n 3210123\n432101234\n 3210123\n  21012\n   101\n    0"]
   [(= n 6) "     0\n    101\n   21012\n  3210123\n 432101234\n54321012345\n 432101234\n  3210123\n   21012\n    101\n    0"]
   [(= n 7) "      0\n     101\n    21012\n   3210123\n  432101234\n 54321012345\n6543210123456\n 54321012345\n  432101234\n   3210123\n    21012\n     101\n      0"]
   [(= n 8) "       0\n      101\n     21012\n    3210123\n   432101234\n  54321012345\n 6543210123456\n765432101234567\n 6543210123456\n  54321012345\n   432101234\n    3210123\n     21012\n      101\n       0"]
   [(= n 9) "\t0\n       101\n      21012\n     3210123\n    432101234\n   54321012345\n  6543210123456\n 765432101234567\n87654321012345678\n 765432101234567\n  6543210123456\n   54321012345\n    432101234\n     3210123\n      21012\n       101\n        0"]
   [(= n 10) "\t 0\n\t101\n       21012\n      3210123\n     432101234\n    54321012345\n   6543210123456\n  765432101234567\n 87654321012345678\n9876543210123456789\n 87654321012345678\n  765432101234567\n   6543210123456\n    54321012345\n     432101234\n      3210123\n       21012\n        101\n         0"]
   [else error "Por favor introduce un número entre 1 y 10"])
  )

;;Función que dado un símbolo lo entierra n número de veces. Es decir,
;;se deberán anidar n − 1 listas hasta que se llegue a la lista que
;;tiene como único elemento al símbolo correspondiente.
;;entierra : symbol number -> list
(define (entierra s n)
  (cond
    [(= n 0) s]
    [else (list (entierra s (- n 1)))]
  ))

[define no-divides? (lambda (x xs) (filter (lambda (a) (or (< a x) (not (= (modulo a x) 0)))) (if (empty? xs) '() (rest xs))))] 
;;Función que encuenta los números primos en un rango de 2 a n
;;usando la Criba de Eratóstenes.
;;criba-eratostenes : number -> (listof number)
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

;;Función que toma un número y regresa una lista de pares con la
;;descomposición en factores primos del mismo.
;;descomposicion-primos : number -> (listof (pairof number))
(define (descomposicion-primos n)
  (let ([primos (criba-eratostenes n)])
    (cond
      [(= n 1) 1]
      [(= (modulo n (first primos)) 0) (cons n (descomposicion-primos (quotient n (first primos))))]
  )))

;;Función que recibe una lista de números entre 0 y 99 regresa una
;;lista con su representación en japones.
;;a-japones : (listof number) -> (listof string)
(define (a-japones n)
  (letrec ([numeros (lambda x
                    (cond
                      [(= x 1) "ichi"]
                      [(= x 2) "ni"]
                      [(= x 3) "san"]
                      [(= x 4) "yon"]
                      [(= x 5) "go"]
                      [(= x 6) "roku"]
                      [(= x 7) "nana"]
                      [(= x 8) "haci"]
                      [(= x 9) "kyu"]
                      [(= x 10) "ju"]
                      [(> x 99) error "Por favor introduce números menores a 100"]
                      [else error "no se puele"]))])
    (cond
      [(= n 0) "rei"]
      [foldr (lambda (x v) (cons x (numeros v))) 0 n]
    )))

;;Función que recibe una lista de números y regresa una nueva lista
;;que contiene únicamente aquellos que son perfectos.
;;perfectos : (listof number) -> (listof number)
(define (perfectos xs) 
  (letrec ([divide? (lambda (x y) (= (modulo y x) 0))]
           [divisores-propios (lambda (n x) (cond
                                              [(> x n) '()]
                                              [(= x n) '()]
                                              [(divide? x n) (cons x (divisores-propios n (+ x 1)))]
                                              [else (divisores-propios n (+ x 1))]))]
           [perfecto? (lambda (n) (= (foldr + 0 (divisores-propios n 1)) n))])
    (filter perfecto? xs)))

;;Función que recibe un número y calcula su serie,
;;n=Sum(1/i!) con i=0 hasta i=n.
;;aproxima : number -> number
(define (aproxima n)
  (letrec ([factorial (lambda x (if (= x 0) 1 (* x (factorial (- x 1)))))]
           [lst (build-list (+ n 1) values)])
    (foldr (lambda (i v) (+ v (/ 1 (factorial i))))
           0 lst)
   ))

;;Función que produce todas las rotaciones de una lista.
;;rota : (listof any) -> (listof (listof any))
(define (rota xs)
  (letrec ([rotacion (lambda (lst) (cons (rest lst)  (first lst)))])
    (foldl (lambda (i v) (rotacion (list v i))) '() xs)))