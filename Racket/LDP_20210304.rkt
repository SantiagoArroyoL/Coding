#lang plai

(let ([a 2] [b 3] [c 4])
  (+ a b c))

(let ([a 2] [b (+ a a)])
  (+ a b))

(let ([a 2])
  (let ([b (+ a a)])
    (+ a b)))

;; let* es azúcar sintáctica de lets anidados
;; let -> with
;; let* -> with*
(let* ([a 2] [b (+ a a)])
  (+ a b))

(let* ([a 2] [b a] [c b] [d c])
  (+ a b c d))

(if (> 10 2)
    3
    (if (> 4 2)
        4
        (if (> 50 30)
            1
            4)))

(cond
   [(> 10 2) 3]
   [(> 4 2) 4]
   [(> 50 30) 1]
   [else 4])

(let* ([b (+ a a)] [a 2])
  b)

(define a 2)


[a 2]

(let ([d 8])
  d)


;; sub1 ::= (- n 1)
;; suman: number -> number
(define (suman n)
  (if (zero? n)
      0
      (+ n (suman (sub1 n)))))

(suman 0)

(suman 1)

(suman 10)

(define (mult n)
  (if (zero? n)
      1
      (* n (mult (sub1 n)))))

(mult 2)

(define (sumad n)
  (if (< n 10)
      n
      (+ (modulo n 10) (sumad (quotient n 10)))))

(sumad 123)

(list 1 2 3)

(cons 1 (cons 2 (cons 3 empty)))

'(1 2 3)

(quote 1 2 3)

(quote (1 2 3))

(list (+ 1 2) (+ 2 3))

(cons (+ 1 2) (cons (+ 2 3) empty))

'((+ 1 2) (+ 2 3))

;; quote se lee como: TÓMALO LITERAL, NO LO INTERPRETES

;; EL PERRO DEL AYUDANTE <- Un ayudante manchado    <- Interpreto
;;                       <- La mascota del ayudante <- Literal

(list '(1 2 3))

'((+ 1 2) (+ 2 3))

;; quote: number, symbol, listas de esas cosas
;; s-expression 

'(+ 1 3)

'1

'foo

(define lista1 '(1 2 3 4 5 6 7 8 9 10))

;; contents of the address register
(car lista1)

;; contents of the decrement register
(cdr lista1)

(first lista1)

(rest lista1)

(car (cdr lista1))

(car (cdr (cdr lista1)))

(cadr lista1)

(caddr lista1)

(empty? lista1)

(null? lista1)

(define (sumal l)
  (if (empty? l)
      0
      (+ (car l) (sumal (cdr l)))))

(sumal '(1 2 3))

(define (multl l)
  (if (empty? l)
      1
      (* (car l) (multl (cdr l)))))

(multl '(1 2 3))


