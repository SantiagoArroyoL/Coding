#|
Compiladores 2023-1
Practica 05 - Tabla de simbolos (rename var)
Equipo: Compilelos
Integrantes:
  Arroyo Lozano Santiago
  Calvario González Berenice
  Liera Montaño Miguel Ángel
|#
#lang nanopass

(require "middle-end.rkt")

(provide (all-defined-out))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Ejercicio 1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Poderosisimo ranme-var
; Si, ranme var
(define-pass rename-var : Jly (ir) -> Jly ()
  (definitions
    (define (generate-next vars name i) ;; Nuevo simbolo
      (define var (string->symbol (string-append (symbol->string name) "_" (number->string i))))
      (if (member var vars) (generate-next vars name (+ i 1)) var))
    ;; Esta es la funcion que como tal genera una nueva variable con un nombre nuevo.
    (define (new-var var tabla)
      ;; Llevamos registro de las vars usadas
      (define used-vars (append (hash-keys tabla) (hash-values tabla)))
      (if (member var used-vars)
          (hash-set! tabla var (generate-next used-vars var 0))
          (hash-set! tabla var var))
      tabla)) ;; CIERRE DEFINITIONS!!!!!!
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Aqui antes tenia dentro de definitios cada nanopass case perono es necesario
  ;; Puede hacer passes de cada metavariable para ir renombrando variables
  ;; Programa
  (Programa : Programa (ir tabla) -> Programa ()
            [(,metodo* ...) `(,(map (lambda (m) (Metodo m tabla)) metodo*) ...)]
            [(,main_exp ,metodo* ...) (let ([newM (MainExp main_exp tabla)]
                                            [newMet* (map (lambda (m) (Metodo m tabla)) metodo*)])
                                        `(,newM ,newMet* ...))])
  ;; Main  
  (MainExp : MainExp (ir tabla) -> MainExp ()
           [(main ,bloque) `(main ,(Bloque bloque tabla))])
  ;; Metodo
  (Metodo : Metodo (ir tabla) -> Metodo ()
          [(,i [ ,declaracion* ... ] ,t ,bloque)
           (let ([newD  (map (lambda (d) (Declaracion d tabla)) declaracion*)]
                 [newB (Bloque bloque tabla)])
             (new-var i tabla)
             `(,(hash-ref tabla i) [ ,newD ... ] ,t ,newB))])
  ;;Bloque
  (Bloque : Bloque (ir tabla) -> Bloque ()
          [{ ,sentencia* ... ,sentencia }
           (let ([newS* (map (lambda (s) (Sentencia s tabla)) sentencia*)]
                 [newS (Sentencia sentencia tabla)])
             `{ ,newS* ... ,newS })])
  ;; Sentencia
  (Sentencia : Sentencia (ir tabla) -> Sentencia ()
             [,while_exp `,(WhileExp while_exp tabla)]
             [,if_exp `,(IfExp if_exp tabla)]
             [,exp `,(Exp exp tabla)]
             [,declaracion `,(Declaracion declaracion tabla)])
  ;; Declaracion
  (Declaracion : Declaracion (ir tabla) -> Declaracion ()
               [(,i ,t) (begin
                          (new-var i tabla)
                          `(,(hash-ref tabla i) ,t))])
  ;; Exp
  (Exp : Exp (ir tabla) -> Exp ()
       [,c `,c]
       [,i `,(hash-ref tabla i)]
       [(,p ,exp1 ,exp2) (let ([newE1 (Exp exp1 tabla)]
                               [newE2 (Exp exp2 tabla)])
                           `(,p ,newE1 ,newE2))]
       [(= (,i ,t) ,exp2) (begin
                            (new-var i tabla)
                            (let ([newI (hash-ref tabla i)]
                                  [newE (Exp exp2 tabla)])
                              `(= (,newI ,t) ,newE)))]
       [(= ,i ,exp2) (let ([newI (hash-ref tabla i)]
                           [newE (Exp exp2 tabla)])
                       `(= ,newI ,newE))]
       [(- ,exp) `(- ,(Exp exp tabla))]
       [(! ,exp) `(! ,(Exp exp tabla))]
       [(return ,exp) `(return ,(Exp exp tabla))]
       [(,i  ,exp* ... ,exp ) (let ([newI (hash-ref tabla i)]
                                      [newE* (map (lambda (e) (Exp e tabla)) exp*)]
                                      [newE (Exp exp tabla)])
                                  `(,newI  ,newE* ... ,newE ))])
  ;; IF exp
  (IfExp : IfExp (ir tabla) -> IfExp ()
         [(if ,exp0 ,exp1 ,exp2) (let ([newE0 (Exp exp0 tabla)]
                                       [newE1 (Exp exp1 tabla)]
                                       [newE2 (Exp exp2 tabla)])
                                   `(if ,newE0 ,newE1 ,newE2))])
  ;; While
  (WhileExp : WhileExp (ir tabla) -> WhileExp ()
            [(while ,exp0 ,bloque) (let ([newE (Exp exp0 tabla)]
                                         [newB (Bloque bloque tabla)])
                                     `(while ,newE ,newB))])
  ;-------------------------> EMPEZAMOS <--------------------------
  (Programa ir (make-hash)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Ejercicio 2 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Casos para cada producción no terminal.
;; Hacemos nanopass case y union de cada tabla que regrese 
; Programa
(define (symbols-programa x tabla)
  (nanopass-case (Jly Programa) x
                 [(,metodo* ...)
                  (let ([set-vars (make-hash)])
                    (foldl
                     (lambda (m s)
                       (union-tablas s (symbol-table-aux m tabla)) s) set-vars metodo*) ;foldl f z l
                    set-vars)]
                 [(,main_exp ,metodo* ...)
                  (let ([set-vars (make-hash)])
                    (union-tablas set-vars (symbol-table-aux main_exp tabla))
                    (foldl (lambda (m s) (union-tablas s (symbol-table-aux m tabla)) s) set-vars metodo*)
                    set-vars)]
                 [else (make-hash)])) ;Si falla, nada

; Main
(define (symbols-main x tabla)
  (nanopass-case (Jly MainExp) x
                 [(main ,bloque) (let ([set-vars (make-hash)])
                                   (union-tablas set-vars (symbol-table-aux bloque tabla))
                                   set-vars)]
                 [else (make-hash)]))

; Metodo
(define (symbols-metodo x tabla)
  (nanopass-case (Jly Metodo) x
                 [(,i [ ,declaracion* ... ] ,t ,bloque)
                  (let* ([set-vars (make-hash `((,i . ,t)))]
                         [args-hash
                          (foldl
                           (lambda (d s)
                             (union-tablas s (symbol-table-aux d tabla)) s) (make-hash) declaracion*)]
                         [args-list
                          (foldr
                           (lambda (d l)
                             (cons
                              `(,(car-decl d)
                                . ,(hash-ref args-hash
                                             (car-decl d))) l)) '() declaracion*)])
                    (hash-set! set-vars i `(,args-list . ,t))
                    (union-tablas set-vars args-hash)
                    (union-tablas set-vars (symbol-table-aux bloque tabla))
                    set-vars)]
                 [else (make-hash)]))

; Bloque
(define (symbols-bloque x tabla)
  (nanopass-case (Jly Bloque) x
      [{,sentencia* ... ,sentencia}
        (let ([set-vars (make-hash)])
          (union-tablas set-vars (symbol-table-aux sentencia tabla))
            (foldl (lambda (sen s)
              (union-tablas s (symbol-table-aux sen tabla)) s) set-vars sentencia*)
          set-vars)]
      [else (make-hash)]))

; Exp
(define (symbols-exp x tabla)
  (nanopass-case (Jly Exp) x
                 [,i (make-hash)]
                 [(,p ,exp1 ,exp2)
                  (let ([set-vars (make-hash)])
                    (union-tablas set-vars (symbol-table-aux exp1 tabla))
                    (union-tablas set-vars (symbol-table-aux exp2 tabla))
                    set-vars)]
                 [(= (,i ,t) ,exp2)
                  (let ([set-vars (make-hash `((,i . ,t)))])
                    (union-tablas set-vars (symbol-table-aux exp2 tabla))
                    set-vars)]
                 [(= ,i ,exp2)
                  (let ([set-vars (make-hash)])
                    (union-tablas set-vars (symbol-table-aux exp2 tabla))
                    set-vars)]
                 [(- ,exp) (symbol-table-aux exp tabla)]
                 [(! ,exp) (symbol-table-aux exp tabla)]
                 [(return ,exp) (symbol-table-aux exp tabla)]
                 [(,i  ,exp* ... ,exp )
                  (let ([set-vars (make-hash)])
                    ;(union-tablas 
                      (union-tablas set-vars (symbol-table-aux exp tabla))
                      (foldl (lambda (e s)
                             (union-tablas s (symbol-table-aux e tabla)) s)
                           set-vars exp*)
                    set-vars)]
                 [else (make-hash)]))

; Declaracion
(define (symbols-declaracion x tabla)
  (nanopass-case (Jly Declaracion) x
                 [(,i ,t) (make-hash `((,i . ,t)))]
                 [else (make-hash)]))

; IfExp
(define (symbols-if x tabla)
  (nanopass-case (Jly IfExp) x
                 [(if ,exp0 ,exp1 ,exp2)
                  (let ([set-vars (make-hash)])
                    (union-tablas set-vars (symbol-table-aux exp0 tabla))
                    (union-tablas set-vars (symbol-table-aux exp1 tabla))
                    (union-tablas set-vars (symbol-table-aux exp2 tabla))
                    set-vars)]
                 [else (make-hash)]))

; WhileExp
(define (symbols-while x tabla)
  (nanopass-case (Jly WhileExp) x
                 [(while ,exp0 ,bloque)
                  (let ([set-vars (make-hash)])
                    (union-tablas set-vars (symbol-table-aux exp0 tabla))
                    (union-tablas set-vars (symbol-table-aux bloque tabla))
                    set-vars)]
                 [else (make-hash)]))

;;;;;;;;;;;;;;;;;;;;;; FUNCIONES AUXILIARES ;;;;;;;;;;;;;;;;;;;;;;
;; Nos regresa el inicio de la delcaracion
(define (car-decl d)
  (nanopass-case (Jly Declaracion) d
                 [(,i ,t) i]))
;; Obtiene la unión de dos tablas hash.
(define (union-tablas one . rest)
  (for* ([two (in-list rest)] [(k v) (in-hash two)])
    (hash-set! one k v)))
;; Esta es como tal, la symbol table
(define (symbol-table e) (symbol-table-aux e (make-hash)))
; Redirige a casos no terminales
(define (symbol-table-aux e tabla)
  (cond
    [(Jly-IfExp? e)       (symbols-if e tabla)]
    [(Jly-Exp? e)         (symbols-exp e tabla)]
    [(Jly-MainExp? e)     (symbols-main e tabla)]
    [(Jly-WhileExp? e)    (symbols-while e tabla)]
    [(Jly-Metodo? e)      (symbols-metodo e tabla)]
    [(Jly-Bloque? e)      (symbols-bloque  e tabla)]
    [(Jly-Programa? e)    (symbols-programa e tabla)]
    [(Jly-Declaracion? e) (symbols-declaracion e tabla)]
    [else (print "erroR")]))


#|
Compiladores 2023-1
Practica 06 - Sistema de Tipos
Equipo: Compilelos
Integrantes:
  Arroyo Lozano Santiago
  Calvario González Berenice
  Liera Montaño Miguel Ángel
|#

; Redirige a casos no terminales
(define (type-check e tabla)
  (cond
    [(Jly-IfExp? e)       (type-if e tabla)]
    [(Jly-Exp? e)         (type-exp e tabla)]
    [(Jly-MainExp? e)     (type-main e tabla)]
    [(Jly-WhileExp? e)    (type-while e tabla)]
    [(Jly-Metodo? e)      (type-metodo e tabla)]
    [(Jly-Bloque? e)      (type-bloque  e tabla)]
    [(Jly-Programa? e)    (type-programa e tabla)]
    [(Jly-Declaracion? e) (type-declaracion e tabla)]))
;; Casos para cada producción no terminal.
; Programa
(define (type-programa x tabla)
  (nanopass-case (Jly Programa) x
                 [(,metodo* ...) (map (lambda (m) (type-check m tabla)) metodo*)]
                 [(,main_exp ,metodo* ...)
                  (map (lambda (m) (type-check m tabla)) (append (list main_exp) metodo*))]))
; Main
(define (type-main x tabla)
  (nanopass-case (Jly MainExp) x
                 [(main ,bloque) (type-check bloque tabla)]))
; Metodo
(define (type-metodo x tabla)
  (nanopass-case (Jly Metodo) x
                 [(,i [ ,declaracion* ... ] ,t ,bloque)
                  (let* ([tipos (hash-ref tabla i)]
                         [bloque-type (type-check bloque tabla)]
                         [method-types (make-hash (car tipos))]
                         [decls-types (map (lambda (d) (type-check d method-types)) declaracion*)]
                         [method-type (cdr tipos)])
                    (if (not (eq? (empty? decls-types) (hash-empty? method-types)))
                        (error "El metodo " i " no debería tener parametros")
                        'unit)
                    (if (eq? bloque-type method-type)
                        (hash-ref tabla i)
                        (error "Método no retorna tipo esperado")))]))
; Bloque
(define (type-bloque x tabla)
  (nanopass-case (Jly Bloque) x
                 [{,sentencia* ... ,sentencia}
                  (let* ([types-ss (map (lambda (s) (type-check s tabla)) sentencia*)]
                         [type-s   (type-check sentencia tabla)]
                         [returns  (filter (lambda (t) (not (eq? 'unit t))) (cons type-s types-ss))])
                    (if (empty? returns)
                        'unit
                        (first returns)))]))
; Exp
(define (type-exp x tabla)
  (nanopass-case (Jly Exp) x
                ;  [(return ,exp) (type-check exp tabla)]
                 [,i (hash-ref tabla i)]
                 [,c (cond
                       [(boolean? c) 'bool]
                       [(number? c)  'int])]
                 [(,p ,exp1 ,exp2)
                  (match p
                    [(or '+ '- '* '/ '%)
                     (let ([t-e1 (type-check exp1 tabla)]
                           [t-e2 (type-check exp2 tabla)])
                       (if (and (eq? t-e1 'int)
                                (eq? t-e2 'int))
                           'int
                           (error "Operandos no son enteros.")))]
                    [(or '< '> '<= '>=) (let ([t-e1 (type-check exp1 tabla)]
                                              [t-e2 (type-check exp2 tabla)])
                                          (if (and (eq? t-e1 'int)
                                                   (eq? t-e2 'int))
                                              'bool
                                              (error "Operandos no son enteros en " exp1 ", " exp2)))]
                    [(or 'AND 'OR) (let ([t-e1 (type-check exp1 tabla)]
                                         [t-e2 (type-check exp2 tabla)])
                                     (if (and (eq? t-e1 'bool)
                                              (eq? t-e2 'bool))
                                         'bool
                                         (error "Operandos no son booleanos en " exp1 ", " exp2)))]
                    [(or '== '!=) (let ([t-e1 (type-check exp1 tabla)]
                                        [t-e2 (type-check exp2 tabla)])
                                    (if (eq? t-e1 t-e2)
                                        'bool
                                        (error "Operandos no son del mismo tipo en " exp1 ", " exp2)))]
                    )]
                 [(= (,i ,t) ,exp2) (let ([decl-type (hash-ref tabla i)]
                                          [type-e    (type-check exp2 tabla)])
                                      (if (not (eq? decl-type t))
                                          (error "Tipo de la variable declarada no coincide para " i)
                                          'unit)
                                      (if (eq? decl-type type-e)
                                          'unit
                                          (error "Expresión asignada difiere del tipo declarado para la variable " i)))]
                 [(= ,i ,exp2) (if (eq? (hash-ref tabla i) (type-check exp2 tabla))
                                   'unit
                                   (error "Expresión asignada difiere del tipo declarado para la variable " i))]
                 [(- ,exp) (if (eq? (type-check exp tabla) 'int)
                               'int
                               (error "- es para resta de enteros. Error en " exp))]
                 [(! ,exp) (if (eq? (type-check exp tabla) 'bool)
                               'bool
                               (error "! es un operador booleano. Error en " exp))]
                 [(,i ,exp* ... ,exp)
                  (if (eq? 'return i) ;Por alguna razon en caso del return se queda aqui atrapado
                    (type-check exp tabla) 
                    (let* ([method-types (hash-ref tabla i)]
                          [parametros (car method-types)]
                          [return-type (cdr method-types)]
                          [param-types (params-types-aux parametros)]
                          [argumentos (map (lambda (e) (type-check e tabla)) (append exp* (list exp)))]
                          [c (andmap (lambda (x y) (eq? x y)) argumentos param-types)])
                      (if c
                          return-type
                          (error "Tipos de argumentos no coinciden con tipos de parámetros. Se esperaba: " parametros))))]))

; Declaracion
(define (type-declaracion x tabla)
  (nanopass-case (Jly Declaracion) x
                 [(,i ,t) (if (eq? (hash-ref tabla i) t)
                              'unit
                              (error "Tipo de la variable declarada no coincide"))]))

; IfExp
(define (type-if x tabla)
  (nanopass-case (Jly IfExp) x
                 [(if ,exp0 ,exp1 ,exp2)
                  (let* ([type-e0 (type-check exp0 tabla)]
                         [type-e1 (type-check exp1 tabla)]
                         [type-e2 (type-check exp2 tabla)])
                    (if (not (eq? type-e0 'bool))
                        (error "Guardia del if no es bool")
                        'unit)
                    (if (not (eq? type-e1 type-e2))
                        (error "Tipos de las subexpresiones del if no coinciden")
                        'unit)
                    type-e1)]))
; WhileExp
(define (type-while x tabla)
  (nanopass-case (Jly WhileExp) x
                 [(while ,exp0 ,bloque) (begin
                                           (type-check bloque tabla)
                                           (if (eq? (type-check exp0 tabla) 'bool)
                                               'unit
                                               (error "Guardia del while no es bool")))]))


;;;;;;;;;;;;;;;;;;;;AUX
(define (params-types-aux l) 
  (if (empty? l)
    '()
    (cons (cdr (car l)) (params-types-aux (cdr l)))))

(define (prepara str) (let ([len (string-length str)])
  (substring str 1 (sub1 len))))


