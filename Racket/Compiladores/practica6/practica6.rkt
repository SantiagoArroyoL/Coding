#|
Compiladores 2023-1
Equipo: Compilelos
Integrantes:
  Arroyo Lozano Santiago
  Calvario González Berenice
  Liera Montaño Miguel Ángel
|#
#lang nanopass

(require "practica4.rkt")
(require "practica5.rkt")

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
                        (error "Método no debe tener parámetros")
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
                                              (error "Operandos no son enteros.")))]
                    [(or 'AND 'OR) (let ([t-e1 (type-check exp1 tabla)]
                                         [t-e2 (type-check exp2 tabla)])
                                     (if (and (eq? t-e1 'bool)
                                              (eq? t-e2 'bool))
                                         'bool
                                         (error "Operandos no son booleanos.")))]
                    [(or '== '!=) (let ([t-e1 (type-check exp1 tabla)]
                                        [t-e2 (type-check exp2 tabla)])
                                    (if (eq? t-e1 t-e2)
                                        'bool
                                        (error "Operandos no son del mismo tipo.")))]
                    )]
                 [(= (,i ,t) ,exp2) (let ([decl-type (hash-ref tabla i)]
                                          [type-e    (type-check exp2 tabla)])
                                      (if (not (eq? decl-type t))
                                          (error "Tipo de la variable declarada no coincide")
                                          'unit)
                                      (if (eq? decl-type type-e)
                                          'unit
                                          (error "Expresión asignada difiere del tipo declarado para la variable")))]
                 [(= ,i ,exp2) (if (eq? (hash-ref tabla i) (type-check exp2 tabla))
                                   'unit
                                   (error "Expresión asignada difiere del tipo declarado para la variable"))]
                 [(- ,exp) (if (eq? (type-check exp tabla) 'int)
                               'int
                               (error "El prefijo - sólo puede afectar a enteros"))]
                 [(! ,exp) (if (eq? (type-check exp tabla) 'bool)
                               'bool
                               (error "El prefijo ! sólo puede afectar a booleanos"))]
                 [(return ,exp) (type-check exp tabla)]
                 [(,i ( ,exp* ... ,exp ))
                  (let* ([args-types   (map (lambda (e) (type-check e tabla)) (append exp* (list exp)))]
                         [method-types (hash-ref tabla i)]
                         [params-types (car method-types)]
                         [return-type  (cdr method-types)]
                         [matches      (andmap (lambda (a p) (eq? a p)) args-types params-types)])
                    (if matches
                        return-type
                        (error "Tipos de argumentos no coinciden con tipos de parámetros")))]))

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



;; PRUEBAS
(define (prueba e)
  (let* ([parseado (parse-Jly (quasiquote ((unquote e))))]
         [renombrado (rename-var parseado)]
         [simbolos (symbol-table renombrado)])
    (type-check renombrado simbolos)))


(define ejemplo-3 '(function [(a int) (b int)] int {
                        (while (!= a 0)
                            {(return a) (b bool) (while (! b) {(return b)})})
                        (return a)
                   }))


;; Si no lanza error, significa que pasamos la verificación de tipos.
(prueba ejemplo-3)
(prueba ejemplo-1)
;(prueba ejemplo-2)
