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


;; Función que genera infinitamente Fibonacci,
;; desde los valores iniciales x ,y
;; FibAux : number number → Stream
(define (fibAux x y)
    (scons (+ x y) (thunk (fibAux y (+ x y)))))

;; Función que genera un Stream llamando a Fibonacci desde 0
;; fib : Stream
(define (fib)
  (scons 0 (thunk (scons 1 (thunk (fibAux 0 1))))))

;; Función que genera una lista infinita ascendente
;; FibAux : number number → Stream
(define (infi n)
  (scons n (thunk (infi (+ n 1)))))