#|
Compiladores
Equipo: Compilelos
Integrantes:
  Arroyo Lozano Santiago
  Calvario González Berenice
  Liera Montaño Miguel Ángel
|#
#lang nanopass

(require "lexer.rkt"
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         (prefix-in re- parser-tools/lex-sre)
         parser-tools/yacc)


(define-struct un-exp (op e1) #:transparent)
(define-struct var-exp (nombre) #:transparent)
(define-struct num-exp (numero) #:transparent)
(define-struct bool-exp (boolean) #:transparent)
(define-struct flujo-exp (op e1) #:transparent)
(define-struct prim-exp (op e1 e2) #:transparent)
(define-struct punt-exp (e1 punt e2) #:transparent)
(define-struct asoc-exp (op1 e op2) #:transparent)

(define compilelos-parser
    (parser
      (start exp) ;Aquí va el simbolo inicial de su gramatica
      (end EOF)   ;Este es el simbolo de final de cadena
      (tokens contenedores vacios) ;Aqui indicamos cuales tokens vamos a usar.
      (error (lambda (tok-ok? tok-name tok-value) ;Mensaje de error simple
    (raise-syntax-error 'error "no fue posible procesar un token" (if tok-value tok-value tok-name)))) ; error
    (precs (nonassoc LP RP LB RB LK RK IF THEN ELSE RETURN WHILE NOT COMMA) ; Sin asociatividad
           (left SUM SUB)
           (right EQ NEQ GT LT GTE LTE OR AND ASSIGN OFTYPE)
           (left MOD)
           (left PROD DIV)) ;Asociatividad der o izq para evitar conflictos con las acciones del algoritmo.
 
      (grammar ;Aquí definimos la gramática!
        (exp ;exp es un simbolo no terminal, que puede convertirse
             ;en una variable o en (exp + exp)
             ; Si recibe exp SUM exp2, entonces $1 = exp, $2 = SUM (No existe), 3$ = exp2
          ;Terminales
          ((VAR) (var-exp $1)) 
          ((NUM) (num-exp $1))
          ((BOOL) (bool-exp $1))
          ;Operaciones
          ((NOT exp) (un-exp 'NOT $2))
          ((exp SUM exp) (prim-exp 'SUM $1 $3))
          ((exp SUB exp) (prim-exp 'SUB $1 $3))
          ((exp PROD exp) (prim-exp 'PROD $1 $3))
          ((exp DIV exp) (prim-exp 'DIV $1 $3))
          ((exp MOD exp) (prim-exp 'MOD $1 $3))
          ((exp LT exp) (prim-exp 'LT $1 $3))
          ((exp GT exp) (prim-exp 'GT $1 $3))
          ((exp LTE exp) (prim-exp 'LTE $1 $3))
          ((exp GTE exp) (prim-exp 'GTE $1 $3))
          ((exp EQ exp) (prim-exp 'EQ $1 $3))
          ((exp NEQ exp) (prim-exp 'NEQ $1 $3))
          ((exp OR exp) (prim-exp 'OR $1 $3))
          ((exp AND exp) (prim-exp 'AND $1 $3))
          ;Puntuacion
          ((LP exp RP) (asoc-exp 'LP $2 'RP))
          ((LB exp RB) (asoc-exp 'LB $2 'RB))
          ((LK exp RK) (asoc-exp 'LK $2 'RK))
          ((exp ASSIGN exp) (punt-exp 'ASSIGN $1 $3))
          ((VAR OFTYPE T-NUM) (punt-exp 'OFTYPE (var-exp $1) 'T-NUM))
          ((VAR OFTYPE T-BOOL) (punt-exp 'OFTYPE (var-exp $1) 'T-BOOL))
          ((exp COMMA exp) (punt-exp $1 'COMMA $3))
          ;Control de flujo
          ((RETURN exp) (flujo-exp 'RETURN $2))
          ((IF exp) (flujo-exp 'IF $2))
          ((THEN exp) (flujo-exp 'THEN $2))
          ((ELSE exp) (flujo-exp 'ELSE $2))
          ((WHILE exp) (flujo-exp 'WHILE $2))
        )
      )
    )
)

;; Función que devuelve el parse de una cadena 
(define (lex-this lexer input) (lambda () (lexer input)))
(let ([input (open-input-string "x:int = 3*(foo+foe)")])
  (compilelos-parser (lex-this compilelos-lexer input)))