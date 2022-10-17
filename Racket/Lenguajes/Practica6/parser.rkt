#lang plai

(require "grammars.rkt")

;; Función que realiza un mapeo entre símbols y funciones.
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
      ['sub1 sub1]
      ['not not]
      ['and (λ args (foldr (λ (x y) (and x y)) #t args))]
      ['or  (λ args (foldr (λ (x y) (or x y)) #f args))]
      ['< <]
      ['> >]
      ['<= <=]
      ['>= >=]
      ['= =]
      ['zero? zero?]
      ['empty? empty?]
      ['car car]
      ['cdr cdr]))

(define operadores '(+ - * / modulo expt add1 sub1 not and or < > <= >= = zero? empty? car cdr))

;; Análisis sintáctico
;; parse: s-expression → SAST
(define (parse sexp)
  (cond
    [(condition? sexp)]
    [(number? sexp) (numS sexp)]
    [(boolean? sexp) (boolS sexp)]
    [(eq? 'empty sexp) (listS '())]
    [(symbol? sexp) (cond
                      [(eq? 'true sexp) (boolS #t)]
                      [(eq? 'false sexp) (boolS #f)]
                      [else (idS sexp)])]
    [(list? sexp) (cond
             [(null? sexp) '()]
             [(number? (car sexp)) (parse-lista sexp)]
             [(eq? 'rec (car sexp)) (recS (parse-bin (second sexp)) (parse (caddr sexp)))]
             [(eq? 'with* (car sexp)) (withS* (parse-bin (second sexp)) (parse (third sexp)))]
             [(eq? 'with (car sexp)) (withS (parse-bin (second sexp)) (parse (third sexp)))]
             [(eq? 'fun (car sexp)) (funS (second sexp) (parse (third sexp)))]
             [(eq? 'if (car sexp)) (ifS (parse (second sexp)) (parse (third sexp)) (parse (third (cdr sexp))))]
             [(eq? 'cond (car sexp)) (condS (parse-cond (cdr sexp)))]
             [(eq? 'list (car sexp)) (listS (parse-lista (cdr sexp)))]
             [(funS? (parse (car sexp))) (appS (parse (car sexp)) (parse-lista (cdr sexp)))]
             [(contiene (car sexp) operadores) (opS (elige (car sexp)) (append (list (parse(second sexp))) (parse-lista (cdr(cdr sexp)))))]
             [else (appS (parse (car sexp)) (parse-lista (cdr sexp)))])]))

;; Funcion auxiliar que hace parse a todos los elementos de una lista
;; parse-lista: (listof s-expression) → (listof SAST)
(define (parse-lista lista)
   (if (null? lista)
       '()
       (append (list (parse(car lista))) (parse-lista (cdr lista)))))

;; Funcion auxiliar que hace parse a todos los elementos de una lista de bindings
;; parse-bin: (listof s-expression) → (listof Binding)
(define (parse-bin bindings)
   (if (null? bindings)
       '()
       (append (list (binding (first (first bindings)) (parse (second (first bindings)))))
               (parse-bin (cdr bindings)))))

;; Funcion auxiliar que hace parse a todos los elementos de una lista de conditions
;; parse-cond: (listof s-expression) → (listof Condition)
(define (parse-cond lista)
   (if (null? (cdr lista))
       (list (else-cond (parse (second (car lista)))))
       (append (list (condition (parse (car (car lista))) (parse (second (car lista)))))
               (parse-cond (cdr lista)))))                       

;; Funcion auxiliar que usa member para decirnos si una lista contiene el elemento m
(define (contiene m lst)
  (if (eq? #f (member m lst)) #f #t))