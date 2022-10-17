#lang plai

;; Definición del tipo Binding.
(define-type Binding
   [binding (id symbol?) (value AST?)])

;; Definición del tipo AST.
(define-type AST
   [id    (i symbol?)]
   [num   (n number?)]
   [op    (f procedure?) (args (listof AST?))]
   [with  (bindings (listof binding?)) (body AST?)]
   [with* (bindings (listof binding?)) (body AST?)])

