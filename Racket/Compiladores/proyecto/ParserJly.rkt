#lang nanopass

(require "LexerJly.rkt"
         racket/enter
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         (prefix-in re- parser-tools/lex-sre)
         parser-tools/yacc)

(provide (all-defined-out))

(define jelly-parser
    (parser
     (start programa) ;Para pobar su funcion expr->string cambien el inicial!
      (end EOF)
      (tokens contenedores vacios)
      (error (lambda (tok-ok? tok-name tok-value)
    (raise-syntax-error 'error "no fue posible procesar un token" (if tok-value tok-value tok-name))))
    (precs (nonassoc LP RP LK RK IF  ELSE ! MAIN COMA)
           (right RETURN)
           (left * / %)
           (left + -)
           (left < > >= <=)
           (left == !=)
           (left &)
           (left OR))

      (grammar
        (programa
            [(metodos) $1]
            [(main) $1]
            [(main metodos) (list* $1 $2)])
        (main
            [(MAIN bloque) (main $2)])
        (metodos
            [(metodo) $1]
            [(metodo metodos) (list* $1 $2)])
        (metodo
            [(id LP declaraciones RP : tipo bloque) (metodo $1 $3 $6 $7)])
        (pexp
            [(LP exp RP) $2])                       
        (id
            [(ID) (id $1)])                         
        (return
            [(RETURN exp) (return $2)])             
        (exp
            [(pexp) $1]                             
            [(id) $1]                               
            [(constante) $1]                        
            [(exp OR exp) (bin-exp 'OR $1 $3)]      
            [(exp & exp) (bin-exp 'AND $1 $3)]      
            [(exp == exp) (bin-exp '== $1 $3)]      
            [(exp != exp) (bin-exp '!= $1 $3)]      
            [(exp < exp) (bin-exp '< $1 $3)]        
            [(exp > exp) (bin-exp '> $1 $3)]        
            [(exp >= exp) (bin-exp '>= $1 $3)]      
            [(exp <= exp) (bin-exp '<= $1 $3)]      
            [(exp + exp) (bin-exp '+ $1 $3)]        
            [(exp - exp) (bin-exp '- $1 $3)]        
            [(exp * exp) (bin-exp '* $1 $3)]        
            [(exp / exp) (bin-exp '/ $1 $3)]        
            [(exp % exp) (bin-exp '% $1 $3)]        
            [(- exp) (un-exp '- $2)]                
            [(! exp) (un-exp '! $2)]
            [(llamada) $1])               

        (stmts
            [(stmt) $1]
            [(stmt stmts) (list* $1 $2)]
            [(stmt SMC stmts) (list* $1 $3)]
            [(stmt SMC) $1])

        (stmt
            [(llamada) $1]                          
            [(while) $1]                            
            [(asignacion) $1]                       
            [(bloque) $1]                           
            [(declaracion) $1]                      
            [(if) $1]                               
            [(return) $1]                           
            )
        (if
          [(IF exp stmt ELSE stmt) (if-exp $2 $3 $5)])

        (while
          [(WHILE exp bloque) (while-exp $2 $3)])   
        (asignacion
            [(declaracion = exp) (bin-exp '= $1 $3)]
            [(id = exp) (bin-exp '= $1 $3)])        
        (declaraciones
            [(declaracion COMA declaraciones) (list* $1 $3)]
            [(declaracion) $1])
        (bloque
            [(LK RK) 'void]
            [(LK stmts RK) $2])
        (declaracion
          [(id : tipo) (decl $1 $3)])
        (constante
            [(NUM)      (num $1)]
            [(BOOLEAN)  (bool $1)])
        (llamada
            [(id LP exps RP) (llamada $1 $3)])
        (exps
            [(exp COMA exps)  (list* $1 $3)]
            [(exp) $1])
        (tipo
            [(INT)    'INT]
            [(BOOL)  'BOOL])
    )))

(define-struct return (exp) #:transparent)
(define-struct if-exp (g t e) #:transparent)
(define-struct decl (id tipo) #:transparent)
(define-struct bool (b) #:transparent)
(define-struct num (n) #:transparent)
(define-struct id (i) #:transparent)
(define-struct un-exp (op o) #:transparent)
(define-struct bin-exp (op o1 o2) #:transparent)
(define-struct llamada (id args) #:transparent)
(define-struct while-exp (g c) #:transparent)
(define-struct main (instrucciones) #:transparent)
(define-struct metodo (id decl-list tipo instrucciones) #:transparent)