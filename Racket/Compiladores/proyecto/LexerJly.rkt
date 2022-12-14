#lang nanopass

(provide (all-defined-out))

(provide contenedores
         vacios
         jelly-lexer)

(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         (prefix-in re- parser-tools/lex-sre)
         parser-tools/yacc
         (for-syntax syntax/parse))

;data Token a = NUM Int | ID String | BOOLEAN Bool
(define-tokens contenedores (NUM ID BOOLEAN))

(define-empty-tokens vacios (;TOKEN        ;LEXEMA
                             ;PalRes
                                MAIN        ;main
                                IF          ;if
                                THEN        ;then
                                ELSE        ;else
                                WHILE       ;while
                                RETURN      ;return
                            ;Tipos
                                INT         ;int
                                BOOL       ;bool
                            ;Pares
                                LP          ;(
                                RP          ;)
                                LK          ;{
                                RK          ;}
                            ;Asignacion
                                =           ;=
                                :           ;:
                            ;Operaciones
                                ! * / % + - < > <= >= == != & OR
                            ;Fin de cadena
                                SMC         ;;
                                COMA        ;,
                                EOF         ;eof
                            ))

(define-lex-trans (epsilon stx)
  (syntax-case stx ()
    [(_) #'""]))

;Alternativa a las expresiones regulares en la definicion del lexer.
(define-lex-trans (pas stx)
   (syntax-case stx ()
     [(_) #'(:or "True" "False")])) 

(define jelly-lexer
  (lexer
    ; [Expresion Regular
    ; Token]

    ;PALABRAS RESERVADAS VAN PRIMERO
        ;control
        [(:: #\,)           (token-COMA)]
        [(:: ";")           (token-SMC)]
        [(:: "main")        (token-MAIN)]
        [(:: "if")          (token-IF)]
        [(:: "else" )       (token-ELSE)]
        [(:: "while")       (token-WHILE)]
        [(:: "return")      (token-RETURN)]
        ;tipos
        [(:: "int")         (token-INT)]
        [(:: "bool")        (token-BOOL)]
        ;parentesis
        [(:: "(" )  (token-LP)]
        [(:: ")" )  (token-RP)]
        [(:: "{" )  (token-LK)]
        [(:: "}" )  (token-RK)]

        ;asignacion
        [(:: #\: )  (token-:)]
        [(:: #\= )  (token-=)]
        ;operaciones
        [(:: #\+ )  (token-+)]
        [(:: #\/ )  (token-/)]
        [(:: #\* )  (token-*)]
        [(:: #\- )  (token--)]
        [(:: #\! )  (token-!)]
        [(:: "!=" ) (token-!=)]
        [(:: "==" ) (token-==)]
        [(:: "%" )  (token-%)]
        [(:: "<=" ) (token-<=)]
        [(:: ">=" ) (token->=)]
        [(:: #\< )  (token-<)]
        [(:: #\> )  (token->)]
        [(:: #\&  ) (token-&)]
        [(:: #\|  ) (token-OR)]

        [(pas)      (token-BOOLEAN lexeme)]

        [(:: (:or #\- (epsilon)) (:+ (char-range #\0 #\9))) ; ([0..9])^+
                    (token-NUM (string->number lexeme))]

        [(:: (:+ (:or (char-range #\a #\z))) ;un identificador inicia con una letra minuscula
         (:* (:or (char-range #\a #\z) (char-range #\A #\Z)
                  (char-range #\0 #\9)
                  (:: #\_)))) ;y se sigue de a..Z num _
                    (token-ID (string->symbol lexeme))]

        [whitespace (jelly-lexer input-port)]
        [(eof)      (token-EOF)]))

(define (lexea s)
  (let* ([input (open-input-string s)])
    (print (jelly-lexer input))))