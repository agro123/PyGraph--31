#lang eopl
;----------------------- Cristian Daniel Medina Ortiz - 2310117

;******************************************************************************************

;; La definición BNF para las expresiones del lenguaje:
;;
;;  <program>      ::= <expression>
;;                      un-program (exp)
;;  <expression>     ::= <number>
;;                      number-lit (datum)
;;                  ::= <identifier>
;;                      var-exp (id)
;;                  ::= (<expression> <prim-binary> <expression>)
;;                       primapp-bin-exp (exp1 prim-binaria exp2)
;;
;;                  ::= <prim-unary> (<expression>)
;;                     primapp-un-exp (prim-unaria exp)
;;                  ::= Si <expression> entonces <expression> sino <expression> finSI
;;                      if-exp (pred-exp true-exp false-exp)
;;                  ::= declarar (identifier = <expression>)* { <expression> }
;;                      const-exp (ids exps cuerpo)
;;                  ::= procedimiento (<identifier>*',') haga <expression> finProc
;;                      procedimiento-ex (ids cuero)
;;                  ::=  "evaluar" expression   (expression ",")*  finEval
;;                        app-exp(exp exps)
;;                  ::= procRecursivo  {<identifier> "(" (<identifier>(,)) ")" "=>" <expression>}* haga <expression> finRec
;;                      rec-exp (nombre ids cuerpo recursion)

;;  <prim-binary> :=  + (primitiva-suma)
;;                      :=  ~ (primitiva-resta)
;;                      :=  / (primitiva-div)
;;                      :=  * (primitiva-multi)
;;                      :=  concat (primitiva-concat)

;;<prim-unary>   :=  longitud (primitiva-longitud)
;;                     :=  add1 (primitiva-add1)
;;                     :=  sub1 (primitiva-sub1)



;****************************************************************************************** Lexica y la gramatica

; / 1. definir la lexica y la gramatica
;Especificación Léxica
(define scanner-spec
'((white-space (whitespace) skip)
  (comment ("//" (arbno (not #\newline))) skip)
  
  (identifier ("@" letter (arbno (or letter digit))) symbol)
  
  (text (letter (arbno (or letter digit whitespace "_" "-" ":" "."))) string)
  (char ((or letter digit)) string)
  
  (number (digit (arbno digit)) number)
  (number ("-" digit (arbno digit)) number)
  (number (digit (arbno digit)) number)
  (number (digit (arbno digit) "." digit (arbno digit)) number)
  (number ("-" digit (arbno digit) "." digit (arbno digit)) number)))

;Especificación Sintáctica (gramática)

(define grammar
  '((program (expression) un-program)

    ;;Identificador
    (expression (identifier) var-exp)

    ;;Definiciones
    (expression ("var " (separated-list identifier "=" expression ",") ";" " in " "{" expression "}") variableLocal-exp)
    (expression ("const " (separated-list identifier "=" expression ",") ";" " in " "{" expression "}") const-exp)
    (expression ("rec " (separated-list identifier "=" expression ",") ";" " in " "{" expression "}") rec-exp)

    ;;Datos
    (expression (number) number-lit)
    (expression ("'"char"'") text-lit)
    (expression ("\""text"\"") text-lit)

    ;;Estructura de control
    (expression ("if (" expression ")" " then {" expression "} else {" expression "}") if-exp)
    (expression ("fun ("  (separated-list identifier ",") ")" "{" expression "}") proc-exp)
    (expression ("%execute :" expression "(" (separated-list expression ",") ")") app-exp)

    ;;Booleanos
    (expression ("FALSE") bool-false)
    (expression ("TRUE") bool-true)

    ;;Primitivas
    (expression ("(" expression prim-binary expression ")") primapp-bin-exp)
    (expression (prim-unary "(" expression ")") primapp-un-exp)
    
    (prim-binary ("+") primitiva-suma)
    (prim-binary ("~") primitiva-resta)
    (prim-binary ("*") primitiva-multi)
    (prim-binary ("/") primitiva-div)
    (prim-binary (" concat ") primitiva-concat)
    (prim-binary ("==") primitiva-igualdad)
    (prim-binary ("!=") primitiva-diferencia)
    
    (prim-unary ("longitud") primitiva-longitud)
    (prim-unary ("add1") primitiva-add1)
    (prim-unary ("sub1") primitiva-sub1)
    ))

; 2. Crear los datatypes con sllgen

(sllgen:make-define-datatypes scanner-spec grammar)

(define show-datatypes
  (lambda () (sllgen:list-define-datatypes scanner-spec grammar))) ;;Visualizar los datatypes

;*******************************************************************************************
; 3. Parser, Scanner, Interfaz

;El FrontEnd (Análisis léxico (scanner) y sintáctico (parser) integrados)
(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar)) ;;Convertir de concreta a abstracta



;El Analizador Léxico (Scanner)
(define just-scan
  (sllgen:make-string-scanner scanner-spec grammar)) ;; Visualizar los tokens

;Entrada de texto del interpretador
(define interpreter
  (sllgen:make-rep-loop  "--> "
    (lambda (pgm) (eval-program  pgm))
    (sllgen:make-stream-parser scanner-spec grammar)))

;******************************************************************************************* Interprete

;;Ambiente inicial
(define init-env
  (lambda ()
    (extend-env
     '(@a @b @c @d @e @PI)
     '(1 2 3 "hola" "FLP" 3.14159265359)
     (empty-env))))

;;Evaluar programa
(define eval-program
  (lambda (pgm)
    (cases program pgm
      (un-program (body)
                   (eval-expression body (init-env)))
      (else (eopl:error "ERROR")))))

;;Evaluar expresion
(define eval-expression
  (lambda (exp env)
    (cases expression exp
      (number-lit (num) num)
      (text-lit (txt) txt)

      (var-exp (id) (buscar-variable env id));; buscar el valor en el ambiente
      (primapp-bin-exp (exp1 prim-binaria exp2) ((eval-binPrim prim-binaria) (eval-expression exp1 env) (eval-expression exp2 env)))
      (primapp-un-exp (prim-unaria exp) ((eval-unaPrim prim-unaria) (eval-expression exp env)))
      
      (if-exp (pred-exp true-exp false-exp)
              (if (valor-verdad? (eval-expression pred-exp env))
                  (eval-expression true-exp env)
                  (eval-expression false-exp env)))
      (const-exp (ids exps cuerpo)
                         (let ((args (list-exps exps env)))
                              (eval-expression cuerpo (extend-env ids args env))))
      (proc-exp (ids cuerpo) (cerradura ids cuerpo env))
      (app-exp (exp exps)
               (let ((proc (eval-expression exp env))
                     (args (list-exps exps env)))
                 (if (procVal? proc)
                     (aplicar-proc proc args)
                     (eopl:error 'eval-expression
                                 "Attempt to apply non-procedure ~s"))))
      (rec-exp (ids exps body)
                   (eval-expression body
                                   (extend-env-rec ids exps env)))
      (bool-false () #f)
      (bool-true () #t)
                     
      (else (eopl:error "ERROR"))
      )))

;******* primitivas
  
;obtener la operacion de  primitiva binaria
(define eval-binPrim 
  (lambda (prim)
    (cases prim-binary prim
      (primitiva-suma () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (+ val1 val2) (eopl:error 'primitiva-suma "Error, esta operacion solo permite numeros"))))
      (primitiva-resta () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (- val1 val2) (eopl:error 'primitiva-resta "Error, esta operacion solo permite numeros"))))
      (primitiva-div () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (/ val1 val2) (eopl:error 'primitiva-div "Error, esta operacion solo permite numeros"))))
      (primitiva-multi () (lambda (val1 val2) (if (and (number? val1) (number? val2)) (* val1 val2) (eopl:error 'primitiva-multi "Error, esta operacion solo permite numeros"))))
      (primitiva-concat () concat)

      (primitiva-igualdad () (lambda (val1 val2) (if (equal? val1 val2) 1 0)))
      (primitiva-diferencia () (lambda (val1 val2) (if (not (equal? val1 val2)) 1 0)))
      (else (eopl:error "ERROR")))))

;obtener la operacion de  primitiva unaria
(define eval-unaPrim 
  (lambda (prim)
    (cases prim-unary prim
      (primitiva-longitud () (lambda (val) (if (string? val) (string-length val) (eopl:error 'longitud "Error, el valor no es una cadena de texto"))))
      (primitiva-add1 () (lambda (val) (if (number? val) (+ val 1) (eopl:error 'add1 "Error, el valor no es un numero"))))
      (primitiva-sub1 () (lambda (val) (if (number? val) (- val 1) (eopl:error 'sub1 "Error, el valor no es un numero"))))
      (else (eopl:error "ERROR"))
      )))
;******************************************************************************************* Ambientes
;Para cualquier valor de scheme retorna true
(define scheme-value? (lambda (v) #t))

;datatype de ambiente
(define-datatype ambiente ambiente?
  (vacio)
  (extendido
   (syms (list-of symbol?))
   (vec (list-of scheme-value?))
   (env ambiente?))
  (rec-env (nombres (list-of symbol?))
             (ids (list-of (list-of symbol?)))
             (cuerpo (list-of expression?))
             (old-env ambiente?)))

;Ambiente vacío
(define empty-env  
  (lambda ()
    (vacio)))

;Extender ambiente
(define extend-env
  (lambda (syms vals env)
    (extendido syms vals env)))

;Buscar un identificador en un ambiente
(define buscar-variable
  (lambda (env sym)
    (cases ambiente env
      (vacio () (eopl:error 'buscar-variable "Error, la variable no existe ~s" sym))
      (extendido (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (buscar-variable env sym))))
      (rec-env (nombres ids cuerpos old-env)
                             (let ((pos (list-find-position sym nombres)))
                                         (if (number? pos)
                                             (cerradura (list-ref ids pos)
                                                        (list-ref cuerpos pos)
                                                         env)
                                             (buscar-variable old-env sym)))))))

;Crea un ambiente extendido para procedimientos recursivos
(define extend-env-rec
  (lambda (ids exps old-env)
    (rec-env ids exps old-env)))

;******************************************************************************************* Procedimientos
;Datatype Procedemiento
(define-datatype procVal procVal?
  (cerradura
   (lista-ID (list-of symbol?))
   (exp expression?)
   (amb ambiente?)))

;Evalua las expresiones de un procedimiento en el ambiente extendido correspondiente
(define aplicar-proc
  (lambda (proc args)
    (cases procVal proc
      (cerradura (ids body env)
               (eval-expression body (extend-env ids args env))))))


;****************************************************************************************  Funciones Auxiliares
; busca la posición de un símbolo en la lista de símbolos de un ambiente
(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))


(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

;Recibe dos valores y retorna una string con su concatenacion
(define concat
  (lambda (val1 val2)
    (cond
      [(number? val1) (concat (number->string val1) val2)]
      [(number? val2) (concat val1 (number->string val2))]
      [(and (string? val1) (string? val2)) (string-append val1 val2)]
      [else (eopl:error 'concat "Error, los valores no son numeros o cadenas")] )))

;Validar si una expresion es verdadera o falsa
(define valor-verdad?
  (lambda (x)
    (not (zero? x))))

;Validar cada expresion en una lista
(define list-exps
  (lambda (exps env)
    (if(eqv? exps empty)
       '()
        (cons (eval-expression (car exps) env) (list-exps (cdr exps) env)))))


;------------------------------------------------Solucion taller------------------------------------------
;A)
;declarar (
;  @radio=2.5;
;  @areaCirculo=procedimiento (@r) haga (@PI*(@r * @r)) finProc
;) { 
;    evaluar @areaCirculo (@radio) finEval  
;}

;B)
;declararRec ( 
;             @factorial= (@n) => Si @n entonces (@n * evaluar @factorial((@n ~ 1)) finEval) sino 1 finSI;
;) {  
;    (("Factorial de 10 es " concat evaluar @factorial(10) finEval) concat ("y Factorial de 5 es " concat evaluar @factorial(5) finEval))
;}

;C)
;declararRec ( 
;        @sumar=(@n,@m) => Si @m entonces evaluar @sumar(add1(@n),sub1(@m)) finEval sino @n finSI;
;) {  
;    evaluar @sumar(4,5) finEval
;}

;D)
;declararRec ( 
;        @restar= (@a,@b) => Si (@b == 0) entonces @a sino evaluar @restar(sub1(@a),sub1(@b)) finEval finSI;
;        @multiplicar= (@a,@b) => Si (@b == 0) entonces 0 sino  (@a + evaluar @multiplicar(@a,sub1(@b)) finEval) finSI;
;) {  
;    (("Restar " concat evaluar @restar(10, 3) finEval) concat ("Multiplicar " concat evaluar @multiplicar(10, 3) finEval))
;}

;E)
;declarar (
;  @integrantes = procedimiento () haga "Cristian Medina" finProc;
;  @saludar = procedimiento (@proc) haga procedimiento () haga ("Hola " concat evaluar @proc() finEval ) finProc finProc
;) { 
;    declarar (
;         @decorate =  evaluar @saludar (@integrantes) finEval  
;    ) { 
;      evaluar @decorate () finEval
;    }
;}

;F)
;declarar (
;  @integrantes = procedimiento (@msf) haga ("Cristian Medina " concat @msf) finProc;
;  @saludar = procedimiento (@proc) haga procedimiento (@adc) haga ("Hola " concat evaluar @proc(@adc) finEval) finProc finProc
;) { 
;    declarar (
;         @decorate =  evaluar @saludar (@integrantes) finEval  
;    ) { 
;      evaluar @decorate ("estudiante de UNIVALLE") finEval
;    }
;}


(interpreter)