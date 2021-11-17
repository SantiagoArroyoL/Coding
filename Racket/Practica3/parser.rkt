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
  (cond
    [(symbol? sexp) (id sexp)]
    [(number? sexp) (num sexp)]
    [(list? sexp) (cond
             [(null? sexp) '()]
             [(number? (car sexp)) (parse-op sexp)]
             [(eq? 'with* (car sexp)) (with* (parse-bin (second sexp)) (parse (third sexp)) )]
             [(eq? 'with (car sexp)) (with (parse-bin (second sexp)) (parse (third sexp)) )]
             [else (op (elige (car sexp)) (append (list (parse(second sexp))) (parse-op (cdr(cdr sexp)))))]
             )]))

;; Funcion auxiliar que hace parse a todos los elementos de una lista
;; parse-op: (listof s-expression) → (listof AST)
(define (parse-op lista)
   (if (null? lista)
       '()
       (append (list (parse(car lista))) (parse-op (cdr lista)))))

;; Funcion auxiliar que hace parse a todos los elementos de una lista de bindings
;; parse-bin: (listof s-expression) → (listof Binding)
(define (parse-bin bindings)
   (if (null? bindings)
       '()
       (append (list (binding (first (first bindings)) (parse (second (first bindings))))) (parse-bin (cdr bindings)))))