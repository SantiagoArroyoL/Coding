#lang plai

;; Predicado para definir estructuras genéricas
;; any ?: any → boolean
(define (any? a) #t)

;; Definición de listas pseudo-infinitas
(define-type Stream
   [sempty]
   [scons (head any?) (tail procedure?)])

;; Función que obtiene el resto de un stream
;; stail : Stream → Stream
(define (stail s)
   ((scons-tail s)))

;; Función que genera una lista infinita de unos
;; unos : Stream
(define (unos) (scons 1 (thunk (unos))))

;; Función que obtiene los primeros n elementos de un stream en forma
;; de lista
;; stake : number Stream → list
(define (stake n l)
(if (zero? n)
    empty
    (cons (scons-head l) (stake (sub1 n) (stail l)))))

(define (sadd xs ys) (scons (+ (scons-head xs) (scons-head ys))
                            (sadd (stail xs) (stail ys))))

(define (fib)
  (scons 0 (scons 1 (sadd (fib) (stail fib)))))

(define (fib)
  (scons 0 (scons 1 (map + (fib) (stail fib)))))