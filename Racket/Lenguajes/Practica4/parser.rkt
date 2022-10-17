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
;; parse: s-expression → SAST
(define (parse sexp)
  (cond
    [(symbol? sexp) (idS sexp)]
    [(number? sexp) (numS sexp)]
    [(list? sexp) (cond
             [(null? sexp) '()]
             [(number? (car sexp)) (parse-op sexp)]
             [(eq? 'with* (car sexp)) (withS* (parse-bin (second sexp)) (parse (third sexp)) )]
             [(eq? 'with (car sexp)) (withS (parse-bin (second sexp)) (parse (third sexp)) )]
             [(eq? 'fun (car sexp)) (funS (second sexp) (parse (third sexp)) )]
             [(funS? (parse (car sexp))) (appS (parse (car sexp)) (parse-op (cdr sexp)))]
             [else (opS (elige (car sexp)) (append (list (parse(second sexp))) (parse-op (cdr(cdr sexp)))))]
             )]))

;; Funcion auxiliar que hace parse a todos los elementos de una lista
;; parse-op: (listof s-expression) → (listof SAST)
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