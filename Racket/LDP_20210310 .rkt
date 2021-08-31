#lang plai

;; Naturales
(define-type Nat
   [cero]
   [suc (n Nat?)])

;; 0
(cero)

;; 1
(suc (cero))

;; 2
(define n (suc (suc (cero))))

(Nat? n)

(Nat? 18)

(cero? (cero))

(cero? n)

(suc-n n)

n

(set-suc-n! n (suc (suc (cero))))

n

;; Suma
(define (suma n m)
  (cond
     [(cero? n) m]
     [else (suma (suc-n n) (suc m))]))

;; Dos formas: type-case (plai), match
(define (suma1 n m)
  (type-case Nat n
    [cero ()  m]
    [suc  (n2) (suma1 n2 (suc m))]))

;; (suc (cero)) (suc (suc (cero)))
;; (cero) (suc (suc (suc (cero))))
;; (suc (suc (suc (cero))))

(define (suma2 n m)
  (match n
    [(cero) m]
    [(suc n) (suma2 n (suc m))]))

;; Apareamiento de patrones, reconocimiento de patrones, caza de patrones,...

;; Multiplicación
;; (+0.5 Tarea) Definir la función multiplicación.
;; 17 de marzo

;; Transformar de Nat a number
(define (Nat->number n)
  (type-case Nat n
    [cero () 0]
    [suc  (n2) (+ 1 (Nat->number n2))]))

(suma2 (suc (cero)) (suc (suc (cero))))

(Nat->number (suc (suc (suc (suc (cero))))))

;; Listas
;; Vacía
;; Cabeza / cola 

(define (any? a) #t)

(define-type Lista
  [vacia]
  [cns (head any?) (tail Lista?)])

;; '(1 2 3)
(define l1 (cns 1 (cns 2 (cns 3 (vacia)))))

;; Longitud
(define (longitud l)
  (type-case Lista l
    [vacia () 0]
    [cns   (h t) (+ 1 (longitud t))]))

;; Concatenación
(define (concatena l1 l2)
  (type-case Lista l1
    [vacia () l2]
    [cns (h t) (cns h (concatena t l2))]))

;; Lista a list (Racket)
(define (Lista->list l)
  (type-case Lista l
      [vacia () empty]
      [cns   (h t) (cons h (Lista->list t))]))

(longitud l1)

(concatena l1 l1)

(Lista->list l1)

;; AE
;;
;; <expr> ::= <num>
;;          | {+ <expr> <expr>}
;;          | {- <expr> <expr>}
;;
;; 1729, 18, 30, ... , {+ 18 35}, {- {+ 20 3} {- 5 6}}, ...
;; SINTAXIS CONCRETA (Lo que escribe el programador)

;; SINTAXIS ABSTRACTA
