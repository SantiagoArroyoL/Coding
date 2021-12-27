#lang plai

;; Definición del tipo Binding.
(define-type Binding
   [binding (id symbol?) (value SAST?)])

;; Definición del tipo SAST.
(define-type SAST
   [idS    (i symbol?)]
   [numS   (n number?)]
   [opS    (f procedure?) (args (listof SAST?))]
   [withS  (bindings (listof binding?)) (body SAST?)]
   [withS* (bindings (listof binding?)) (body SAST?)]
   [funS   (params (listof symbol?)) (body SAST?)]
   [appS   (fun-expr SAST?) (args (listof SAST?))])

;; Definición del tipo AST.
(define-type AST
   [id   (i symbol?)]
   [num  (n number?)]
   [op   (f procedure?) (args (listof AST?))]
   [fun  (param symbol?) (body AST?)]
   [app  (fun-expr AST?) (arg AST?)])

;; Resultados del intérprete.
(define-type AST-Value
   [numV     (n number?)]
   [closureV (param symbol?) (body AST?) (env Env?)])

;; Definición de ambientes de evaluación.
(define-type Env
   [mtSub]
   [aSub (id symbol?) (value AST-Value?) (rest-env Env?)])