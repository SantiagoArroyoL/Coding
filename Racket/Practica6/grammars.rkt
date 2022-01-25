#lang plai

;; Definición del tipo Binding.
(define-type Binding
   [binding (id symbol?) (value SAST?)])

;; Definición del tipo Condition.
(define-type Condition
   [condition (test-expr SAST?) (then-expr SAST?)]
   [else-cond (else-expr SAST?)])

;; Definición del tipo SAST.
(define-type SAST
   [idS    (i symbol?)]
   [numS   (n number?)]
   [boolS  (b boolean?)]
   [listS  (elems (listof SAST?))]
   [opS    (f procedure?) (args (listof SAST?))]
   [ifS    (test-expr SAST?) (then-expr SAST?) (else-expr SAST?)]
   [condS  (cases (listof Condition?))]
   [withS  (bindings (listof binding?)) (body SAST?)]
   [withS* (bindings (listof binding?)) (body SAST?)]
   [recS   (bindings (listof binding?)) (body SAST?)]
   [funS   (params (listof symbol?)) (body SAST?)]
   [appS   (fun-expr SAST?) (args (listof SAST?))])

;; Definición del tipo AST.
(define-type AST
   [id   (i symbol?)]
   [num  (n number?)]
   [bool (b boolean?)]
   [lisT (elems (listof AST?))]
   [op   (f procedure?) (args (listof AST?))]
   [iF   (test-expr AST?) (then-expr AST?) (else-expr AST?)]
   [fun  (param symbol?) (body AST?)]
   [app  (fun-expr AST?) (arg AST?)])

;; Resultados del intérprete.
(define-type AST-Value
   [numV     (n number?)]
   [boolV    (b boolean?)]
   [listV    (elems (listof AST-Value?))]
   [closureV (param symbol?) (body AST?) (env Env?)]
   [exprV    (expr AST?) (env Env?)])

;; Definición de ambientes de evaluación.
(define-type Env
   [mtSub]
   [aSub    (id symbol?) (value AST-Value?) (rest-env Env?)])
