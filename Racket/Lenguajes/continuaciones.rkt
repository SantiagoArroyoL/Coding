#lang plai
;; suma-list : ( listof number ) → number
(define (suma-list lst) 
  (suma-list-cps lst (λ (x) x)))

;; suma-list : ( listof number ) procedure → number
(define (suma-list-cps lst k)
  (match lst
    ['() (k 0)]
    [( cons x xs ) (suma-list-cps xs (λ (v) (k (+ x v))))]))

;; Continuaciones
(+
( expt 7 2)
( expt 7 3)
( let/cc k ( k ( expt 7 4)))
( expt 7 5))

;; Tarea06
(define c #f)
(+ 1 (+ 2 (+ 3 (+ (let/cc k (set! c k) 4) 5))))
(c 10)