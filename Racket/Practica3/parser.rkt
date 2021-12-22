#lang plai

(require "grammars.rkt")

;; Función que realiza un mapeo entre símbolos y funciones.
;; elige: symbol → procedure
(define (elige s)
   (match s
      ['+ +]
      ['- -]
      ['* *]
      ['/ /]
      ['modulo modulo]
      ['expt expt]
      ['add1 add1]
      ['sub1 sub1]))

;; Análisis sintáctico
;; parse: s-expression → AST
(define (parse sexp)
  "escribe aquí tu codigo")
 