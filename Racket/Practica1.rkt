#lang plai
;; Practica1 - Arroyo Lozano Santiago
;; 317150700

;; 1. Predicado que nos dice si un numero es negativo
;; neg?: number -> Boolean
(define (neg? a)
  (if (> a 0)
    #f
       #t))

(neg? -3)

;; 2. Predicado que nos dice si un numero es par
;; esPar?: numner -> boolean
(define (esPar? n)
  (if (= (modulo n 2) 0)
    #t
       #f))

(esPar? -2)

(esPar? 0)

;; 3. Procedimiento que nos devuelve el valor absoluto de un número
;; absoluto: number -> number
(define (absoluto n)
  (if (< n 0)
    (* n -1)
       n))

(absoluto -5)

;; 4. Procedimiento que calcula el area de un cono de base circular
;; area-cono: number number -> number
(define (area-cono d g)
  (define r (/ d 2))
  (+ (* (* pi r) g)(* (expt r 2) pi)))

(area-cono 10 15)

;; 5. Procedimiento que eleva el numero a, a la potencia b
;; potencia: number number
(define (potencia a b)
  2)

(potencia 2 -3)
