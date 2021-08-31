#lang plai

;; Sintaxis Concreta
;; Lenguaje AE
;; <expr> ::= <id>
;;          | <num>
;;          | {+ <expr> <expr>}
;;          | {- <expr> <expr>}

;; Sintaxis Abstracta
(define-type ASA
  [id (i symbol?)]
  [num (n number?)]
  [add (i ASA?) (d ASA?)]
  [sub (i ASA?) (d ASA?)])

;; interp: ASA -> number
;; Intérprete para AE, toma una expresión en sintaxis abstracta y nos devuelve el resultado de
;; evaluar dicha expresión.
(define (interp expr)
  (match expr
    [(num n)
        n]
    [(add i d)
        (+ (interp i) (interp d))]
    [(sub i d)
        (- (interp i) (interp d))]))
