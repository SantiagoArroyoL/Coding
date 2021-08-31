#lang plai

;; Sintaxis Concreta
;; Lenguaje WAE
;; <expr> ::= <id>
;;          | <num>
;;          | {+ <expr> <expr>}
;;          | {- <expr> <expr>}
;;          | {with {<id> <expr>} <expr>}

;; Sintaxis Abstracta
(define-type ASA
  [id (i symbol?)]
  [num (n number?)]
  [add (i ASA?) (d ASA?)]
  [sub (i ASA?) (d ASA?)]
  [with (id symbol?) (value ASA?) (body ASA?)])

;; interp: ASA -> ASA
;; Intérprete para FWAE, toma una expresión en sintaxis abstracta y nos devuelve el resultado de
;; evaluar dicha expresión.
(define (interp expr)
  (match expr
    [(id i)
        (error 'interp "Variable libre")]
    [(num n)
        (num n)]
    [(add i d)
        (num (+ (num-n (interp i)) (num-n (interp d))))]
    [(sub i d)
        (num (- (num-n (interp i)) (num-n (interp d))))]
    [(with id value body)
        (interp (subst body id (interp value)))]))

;; subst: ASA symbol ASA -> ASA
;; Algoritmo de sustitución modificado para soportar funciones y aplicaciones de función.
(define (subst expr sub-id val)
  (match expr
    [(id i)
        (if (equal? i sub-id) val expr)]
    [(num n)
        expr]
    [(add i d)
        (add (subst i sub-id val) (subst d sub-id val))]
    [(sub i d)
        (sub (subst i sub-id val) (subst d sub-id val))]
    [(with id value body)
        (if (equal? id sub-id)
            (with id (subst value sub-id val) body)
            (with id (subst value sub-id val) (subst body sub-id val)))]))
