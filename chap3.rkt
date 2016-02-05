#lang eopl

(require "./chap2.rkt")
(require  "./chap2-from-section2.4-to-end.rkt")

;;;redefine environment for section3.4 LETREC Language

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val expval?)
   (env environment?))

  (extend-env-rec
   (p-names (list-of identifier?))
   (procs-vars (list-of (list-of identifier?)))
   (p-bodys (list-of expression?))
   (env environment?))
  )

(define apply-env
  (lambda (env search-var)
     (define apply-env-mutually-rec
        (lambda (search-var p-names procs-vars p-bodys saved-env env)
          (if (null? p-names)
              (apply-env env search-var)
              (if (eqv? (car p-names) search-var)
                  (proc-val (procedure (car procs-vars) (car p-bodys) env))
                  (apply-env-mutually-rec search-var (cdr p-names) (cdr procs-vars) (cdr p-bodys) saved-env env)))))
    (cases environment env
      (empty-env () report-no-binding-found search-var)
      (extend-env (var val saved-env)
                  (if (eqv? var search-var)
                      val
                      (apply-env saved-env search-var)))
    
      (extend-env-rec (p-names procs-vars p-bodys saved-env)
                               (apply-env-mutually-rec search-var p-names procs-vars p-bodys saved-env env))
      )))

;;section3.2 LET: A Simple Language

(define-datatype program program?
  (a-program (exp expression?)))


(define-datatype expression expression?
  (const-exp (num number?))
  (minus-exp (exp expression?))
  (diff-exp (exp1 expression?) (exp2 expression?))
  (add-exp (exp1 expression?) (exp2 expression?))
  (multiply-exp (exp1 expression?) (exp2 expression?))
  (quotient-exp (exp1 expression?) (exp2 expression?))
  (bool-exp (exp1 boolexpression?))
  (if-bool-exp (exp1 boolexpression?) (exp2 expression?) (exp3 expression?))
  (var-exp (var identifier?))
  (let-exp (vars (list-of identifier?)) (exps (list-of expression?)) (body expression?))
  (let*-exp (vars (list-of identifier?)) (exps (list-of expression?)) (body expression?))
  (emptylist-exp)
  (cons-exp (exp1 expression?) (exp2 expression?))
  (car-exp (exp expression?))
  (cdr-exp (exp expression?))
  (list-exp (exps (list-of expression?)))
  (cond-exp (preds (list-of boolexpression?)) (consequences (list-of expression?)))
  (print-exp (exp expression?))
  (unpack-exp (vars (list-of identifier?)) (exp1 expression?) (body expression?))
  (proc-exp (vars (list-of identifier?)) (body expression?))
  (call-exp (rator expression?) (rands (list-of expression?)))
  (letproc-exp (proc-name identifier?) (vars (list-of identifier?)) (proc-body expression?) (body expression?))
  (traceproc-exp (vars (list-of identifier?)) (body expression?))
  (dynamic-binding-proc-exp (vars (list-of identifier?)) (body expression?))
  (letrec-exp (proc-names (list-of identifier?)) (procs-vars (list-of (list-of identifier?))) (proc-bodys (list-of expression?)) (letrec-body expression?))

  ;;used for lexical addressing
  (nameless-var-exp (index integer?))
  (nameless-let-exp (exps (list-of expression?)) (body expression?))
  (nameless-let*-exp (exps (list-of expression?)) (body expression?))
  (nameless-proc-exp (body expression?))
  (nameless-unpack-exp (exp expression?) (body expression?))
  (nameless-letproc-exp (proc-body expression?) (body expression?))
  (nameless-traceproc-exp (body expression?))
  
  

  )

(define-datatype boolexpression boolexpression?
  (equal?-bool-exp (exp1 expression?) (exp2 expression?))
  (greater?-bool-exp (exp1 expression?) (exp2 expression?))
  (less?-bool-exp (exp1 expression?) (exp2 expression?))
  (zero?-bool-exp (exp1 expression?))
  (null?-bool-exp (exp expression?))
  )

;;define expressed value
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (list-val (list (list-of expval?)))
  (proc-val (proc proc?))
  ;;added for nameless interpreter
  (nameless-proc-val (nameless-proc nameless-proc?))
  )


(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (eopl:error 'expval->num "not a num value.~s" val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (eopl:error 'expval->bool "not a bool value.~s" val)))))

(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (list) list)
      (else (eopl:error 'expval->list "not a list value.~s" val)))))

(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (eopl:error 'expval->proc "not a proc value.~s" val)))))

(define expval->nameless-proc
  (lambda (val)
    (cases expval val
      (nameless-proc-val (nameless-proc) nameless-proc)
      (else (eopl:error 'expval->proc "not a nameless-proc value.~s" val)))))
 

;;setup the init environment

(define init-env
  (lambda ()
    (extend-env 'i (num-val 1)
                (extend-env 'v (num-val 5)
                            (extend-env 'x (num-val 10)
                                        (empty-env))))))

;;inteprete the program

(define value-of-program
  (lambda (prog)
    (cases program prog
      (a-program (exp)
                 (value-of exp (init-env))))))


;;evalute bool expression
(define value-of-bool-exp
      (lambda (exp env)
        (define compare-operation
          (lambda (op exp1 exp2 env)
            (let ((val1 (value-of exp1 env))
                  (val2 (value-of exp2 env)))
              (bool-val (op (expval->num val1) (expval->num val2))))))
        (cases boolexpression exp
          (equal?-bool-exp (exp1 exp2)
                           (compare-operation eqv? exp1 exp2 env))
          (greater?-bool-exp (exp1 exp2)
                             (compare-operation > exp1 exp2 env))
          (less?-bool-exp (exp1 exp2)
                          (compare-operation < exp1 exp2 env))
          (zero?-bool-exp (exp)
                          (bool-val (zero? (expval->num (value-of exp env)))))
          (null?-bool-exp (exp)
                          (bool-val (null? (expval->list (value-of exp env))))))))

(define value-of
  (lambda (exp env)
    (define arithmetic-operation
      (lambda (op exp1 exp2 env)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (num-val (op (expval->num val1) (expval->num val2))))))
    (define evaluate-list-exp
      (lambda (exps env)
        (if (null? exps)
            (list-val '())
            (list-val (cons (value-of (car exps) env)
                            (expval->list (evaluate-list-exp (cdr exps) env)))))))
    (define evaluate-cond-exp
      (lambda (preds cons env)
        (if (null? preds)
            (eopl:error 'value-of "none of the cond expression's test condition success")
            (if (expval->bool (value-of-bool-exp (car preds) env))
                (value-of (car cons) env)
                (evaluate-cond-exp (cdr preds) (cdr cons) env)))))

    (define evaluate-let-exp
      (lambda (vars exps body-exp argenv finalenv)
        (if (null? vars)
            (value-of body-exp finalenv)
            (evaluate-let-exp (cdr vars)
                              (cdr exps)
                              body-exp
                              argenv
                              (extend-env (car vars) (value-of (car exps) argenv) finalenv)))))
    (define evaluate-let*-exp
      (lambda (vars exps body-exp env)
        (if (null? vars)
            (value-of body-exp env)
            (evaluate-let*-exp (cdr vars)
                               (cdr exps)
                               body-exp
                               (extend-env (car vars) (value-of (car exps) env) env)))))

    (define evaluate-call-exp-rands
      (lambda (rands env)
        (if (null? rands)
            '()
            (cons (value-of (car rands) env)
                  (evaluate-call-exp-rands (cdr rands) env)))))

    (cases expression exp
      (const-exp (num) (num-val num))
      (minus-exp (exp) (num-val (- 0 (expval->num (value-of exp env)))))
      (var-exp (var) (apply-env env var))
      (diff-exp (exp1 exp2)
                (arithmetic-operation - exp1 exp2 env))
      
      (add-exp (exp1 exp2)
               (arithmetic-operation + exp1 exp2 env))
     
      (multiply-exp (exp1 exp2)
                    (arithmetic-operation * exp1 exp2 env))
      
      (quotient-exp (exp1 exp2)
                    (arithmetic-operation remainder exp1 exp2 env))
      
      (if-bool-exp (boolexp exp2 exp3)
             (if (expval->bool (value-of-bool-exp boolexp env))
                 (value-of exp2 env)
                 (value-of exp3 env)))

      (bool-exp (exp)
                (value-of-bool-exp exp env))
              
      (let-exp (vars exps body)
               (evaluate-let-exp vars exps body env env))

      (let*-exp (vars exps body)
                (evaluate-let*-exp vars exps body env))
      
      (emptylist-exp () (list-val '()))
      (car-exp (exp)
               (let ((val (value-of exp env)))
                 (car (expval->list val))))
      (cdr-exp (exp)
               (let ((val (value-of exp env)))
                 (list-val (cdr (expval->list val)))))
      
      (cons-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (list-val (cons val1 (expval->list val2)))))
      (list-exp (exps)
                (evaluate-list-exp exps env))
      (cond-exp (preds consequences)
                (evaluate-cond-exp preds consequences env))
      (print-exp (exp)
                 (begin (eopl:printf "~s" (value-of exp env)) (num-val 1)))
      (unpack-exp (vars exp1 body)
                  (let ((vals (expval->list (value-of exp1 env))))
                    (if (not (eqv? (length vars) (length vals)))
                        (eopl:error 'unpack-exp "number of vars do not match the list element length in expression:~s" exp)
                        (value-of body (extend-multivars-env vars vals env)))))
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      (call-exp (rator rands)
                (apply-procedure (expval->proc (value-of rator env)) (evaluate-call-exp-rands rands env) env))
      (letproc-exp (proc-name vars proc-body body)
                   (value-of body (extend-env proc-name (proc-val (procedure vars proc-body env)) env)))
      (traceproc-exp (vars body)
                     (proc-val (trace-procedure vars body env)))
      (dynamic-binding-proc-exp (vars body)
                                (proc-val (dynamic-binding-procedure vars body)))
      (letrec-exp (p-names procs-vars p-bodys letrec-body)
                  (value-of letrec-body (extend-env-rec p-names procs-vars p-bodys env)))
      ;;lexical addressing; any occurence of the nameless expression we'll report an error
      (else
       (eopl:error 'value-of "occurence of nameless exp:~s" exp))

      )))

;; some helper procedures
(define extend-multivars-env
                      (lambda (vars vals env)
                        (if (null? vars)
                            env
                            (extend-env (car vars)
                                        (car vals)
                                        (extend-multivars-env (cdr vars) (cdr vals) env)))))

;; lexical spec

(define lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

;; grammer-spec
(define grammer-spec
  '(
    (program (expression) a-program)
    (expression (number) const-exp)
    (expression (identifier) var-exp)
    (expression (boolexpression) bool-exp)
    (expression ("minus" "(" expression ")") minus-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" expression "," expression ")") add-exp)
    (expression ("*" "(" expression "," expression ")") multiply-exp)
    (expression ("//" "(" expression "," expression ")") quotient-exp)
    (expression ("if" boolexpression "then" expression "else" expression) if-bool-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("cond" "{" (arbno boolexpression "==>" expression) "}" "end") cond-exp)
    (expression ("print" "(" expression ")") print-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letproc" identifier "(" (separated-list identifier ",") ")" expression "in" expression) letproc-exp)
    (expression ("traceproc" "(" (separated-list identifier ",") ")" expression) traceproc-exp)
    (expression ("dynamicproc" "(" (separated-list identifier ",") ")" expression) dynamic-binding-proc-exp)
    (expression ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression) letrec-exp)
    
    (boolexpression ("equal?" "(" expression "," expression ")") equal?-bool-exp)
    (boolexpression ("zero?" "(" expression ")") zero?-bool-exp)
    (boolexpression ("greater?" "(" expression "," expression ")") greater?-bool-exp)
    (boolexpression ("less?" "(" expression "," expression ")") less?-bool-exp)
    (boolexpression ("null?" "(" expression ")") null?-bool-exp)
    
    ))

(define scan&parse
    (sllgen:make-string-parser lexical-spec grammer-spec))

(provide scan&parse)

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(provide run)

(define testp "let x = 1 in if zero?(-(x,i)) then 10 else 100")

;;test for exercise3.6
(run " minus(-(minus(5),9))")

;;test for exercise3.7
(run "+(//(13,4),*(minus(3), 2))")

;;test for exercise3.8
(run "equal?(//(13,4),minus(minus(1)))")
(run "equal?(//(minus(13),4),minus(minus(1)))")

(run "greater?(//(13,4),minus(2))")
(run "less?(//(13,4),minus(2))")
(run "greater?(//(13,minus(4)),2)")
(run "less?(//(13,minus(4)),2)")

;;test for exercise3.9
;;test for cons
(run "let x = 4 in cons(x,cons(cons(-(x,1),emptylist),emptylist))")

;;test for car 
(run "let y = let x = 4 in cons(x,cons(cons(-(x,1),emptylist),emptylist)) in car(y)")

;;test for cdr
(run "let y = let x = 4 in cons(x,cons(cons(-(x,1),emptylist),emptylist)) in cdr(y)")

;;test for null?
(run "null?(cons(1,emptylist))")
(run "null?(emptylist)")

;;test for exercise3.10
(run "let x = 4 in list(x,-(x,1),-(x,3))")

;;test for exercise3.12
(run "cond { zero?(1) ==> 1
             greater?(2,3) ==> 2
             less?(3,1) ==> 3
             null?(emptylist) ==> 4
             greater?(3,1) ==> 5 } end ")


(run "if equal?(1,1) then 1 else 2")

;;test for exercise3.15
(run "let a = 1 in print(let b = 1 in cond {
                                    zero?(a) ==> 0
                                    greater?(a,i) ==> 1
                                    zero?(-(a,i)) ==> 2
                                    } end )")

;;test for exercise3.16
(run "let x = 30 in let x = -(x,1) y = -(x,2) in -(x,y)")
(run "let x = 30 in let a = let x = -(x,1) y = -(x,2) in -(x,y) b = 2 in -(a,b)")



;;test for exercise 3.17
(run "let x = 30 in let* x= -(x,1) y = -(x,2) in -(x,y)")
(run "let x = 30 in let* a = let x = -(x,1) y = -(x,2) in -(x,y) b = 2 in -(a,b)")


;;test for exercise3.18
(run "let u = 7 in unpack x y = cons(u,cons(3,emptylist)) in -(x,y)")

;;;error exercise
;(run "let u = 7 in unpack x y z = cons(u,cons(3,emptylist)) in -(x,y)")



;;begin of section3.3
(display "begin of section3.3 the PROC Language")
(newline)

(define-datatype proc proc?
  (procedure (vars (list-of identifier?))
             (body expression?)
             (saved-env environment?))
  (trace-procedure (vars (list-of identifier?))
                   (body expression?)
                   (saved-env environment?))
  (dynamic-binding-procedure (vars (list-of identifier?))
                             (body expression?))
  )



(define apply-procedure
  (lambda (proc1 args env)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of body (extend-multivars-env vars args saved-env)))
      (dynamic-binding-procedure (vars body)
                 (value-of body (extend-multivars-env vars args env))) ;;dynamic binding, evaluate the body with current environment.
      (trace-procedure (vars body saved-env)
                       (begin (eopl:printf "entering func")
                              (newline)
                              (let ((r (value-of body (extend-multivars-env vars args saved-env))))
                                (begin (eopl:printf "exiting func")
                                       (newline)
                                       r)))))))

;;test for basiec PROC Language
(run "let f = proc(x) -(x,1) in (f (f 77))")
(run "let x = 200
      in let f = proc (z) -(z,x)
         in let x = 100
            in let g = proc (z) -(z,x)
               in -((f 1), (g 1))")

(run "letproc f (x) -(x,1) in (f (f 77))")

;;exercise 3.20
(run "let f = proc (x) proc (y) +(x,y) in ((f 3) 4)")


;;test for exercise 3.21
(run "let f = proc (x,y,z) proc (u) +(u,+(x,+(y,z))) in
((f 1 2 3) 4)")

(run "letproc f (x,y,z) +(x,+(y,z)) in (f 1 2 3)")

;;exercise3.23
(run "let makemult = proc (maker) proc (x)
if zero?(x)
then 0
else -(((maker maker) -(x,1)), minus(4))
in let timesfour = proc (x) ((makemult makemult) x) in (timesfour 3)")

(display (run "let makemultn = proc (n)
             proc(maker) proc (x)
              if zero?(x)
                 then 0
                 else +(((maker maker) -(x,1)), n)
      in let timesn = proc (n)
                      let f = (makemultn n) in
                      proc (x) 
                          ((f f) x) in
                             let fact = proc (n , factfunc)
                                 if zero?(n)
                                    then 1
                                    else ((timesn (factfunc -(n,1) factfunc)) n)
                               in (fact 10 fact)"))
                             
(define fact
  (lambda (n)
    (if (zero? n)
        1
        (* n (fact (- n 1))))))

;;; the trick Currying is used to support multiple params func.
;;; if we do not support multiple params func in our language grammer we can use Currying to achieve the same effect.

;;test for exercise 3.27
(run "let f = traceproc (x) traceproc (y) +(x,y) in ((f 3) 4)")
(run "let f = traceproc (x,g) +(1,(g x))
 g = traceproc(y) y in
 (f 2 g)")

    
(run " let a = 3
      in let p = dynamicproc (x) -(x,a)
a=5
in -(a,(p 2))")

(run "let a = 3
      in let p = dynamicproc (z) a
         in let f = dynamicproc (x) (p 0)
            in let a = 5
in (f 2)")

;;;section3.4 LETREC Language

                 
(run "letrec double(x) = if zero?(x) then 0 else +((double -(x,1)), 2) in (double 6)")

;;test for exercise3.31
(run "letrec double(x,y) = if zero?(x) then 0 else +(y,+((double -(x,1) y), 2)) in (double 6 2)")


;;test for exercise 3.32/3.33
(run "letrec
even(x) = if zero?(x) then 1 else (odd -(x,1))
odd(x) = if zero?(x) then 0 else (even -(x,1))
in (odd 12)")

;;exercise 3.37
;;for test
(run "let fact = proc (n) +(n,1) in let fact = proc (n)
                          if zero?(n)
                          then 1
                          else *(n,(fact -(n,1)))
in (fact 5)")

(run "let fact = dynamicproc (n) +(n,1) in let fact = dynamicproc (n)
                          if zero?(n)
                          then 1
                          else *(n,(fact -(n,1)))
in (fact 6)")
;;implement 3.37
(run
 " let even = dynamicproc(x) if zero?(x) then 1 else (odd -(x,1))
    in let odd = dynamicproc(x) if zero?(x) then 0 else (even -(x,1))
       in (odd 13)")


;;;section3.7
(define empty-senv
  (lambda ()
    '()))

(define extend-senv
  (lambda (var senv)
    (cons var senv)))

(define apply-senv
  (lambda (senv search-var)
    (cond ((null? senv) (report-no-binding-found search-var))
          ((eqv? search-var (car senv)) 0)
          (else (+ 1 (apply-senv (cdr senv) search-var))))))

(define init-senv
  (lambda ()
    (extend-senv 'i
                 (extend-senv 'v
                              (extend-senv 'x
                                           (empty-senv))))))

(define translation-of-bool-exp
  (lambda (bexp senv)
    (cases boolexpression bexp
      (equal?-bool-exp (exp1 exp2)
                       (equal?-bool-exp (translation-of exp1 senv) (translation-of exp2 senv)))
      (greater?-bool-exp (exp1 exp2)
                         (greater?-bool-exp (translation-of exp1 senv) (translation-of exp2 senv)))
      (less?-bool-exp (exp1 exp2)
                      (less?-bool-exp (translation-of exp1 senv) (translation-of exp2 senv)))
      (zero?-bool-exp (exp)
                      (zero?-bool-exp (translation-of exp senv)))
      (null?-bool-exp (exp)
                      (null?-bool-exp (translation-of exp senv))))))


(define translation-of
  (lambda (inexp senv)

    (define translation-of-let
      (lambda (exps senv)
        (if (null? exps)
            '()
            (cons (translation-of (car exps) senv)
                  (translation-of-let (cdr exps) senv)))))

    (define extend-multivars-senv
      (lambda (vars senv)
        (if (null? vars)
            senv
            (cons (car vars)
                  (extend-multivars-senv (cdr vars) senv)))))

    (define translation-of-let*
      (lambda (vars exps senv)
        (cond ((null? exps) '())
              ((null? (cdr exps)) (list (translation-of (car exps) senv)))
              (else (cons (translation-of (car exps) senv)
                         (translation-of-let* (cdr vars) (cdr exps) (extend-senv (car vars) senv)))))))

    (define translation-of-exps
      (lambda (exps senv)
        (if (null? exps)
            '()
            (cons (translation-of (car exps) senv)
                  (translation-of-exps (cdr exps) senv)))))

    (define translation-of-boolexps
      (lambda (bexps senv)
        (if (null? bexps)
            '()
            (cons (translation-of-bool-exp (car bexps) senv)
                  (translation-of-boolexps (cdr bexps) senv)))))
    
    (cases expression inexp
      (const-exp (num) (const-exp num))
      (minus-exp (exp) (minus-exp (translation-of exp senv)))
      (diff-exp (exp1 exp2) (diff-exp (translation-of exp1 senv) (translation-of exp2 senv)))
      (add-exp (exp1 exp2) (add-exp (translation-of exp1 senv) (translation-of exp2 senv)))
      (multiply-exp (exp1 exp2) (multiply-exp (translation-of exp1 senv) (translation-of exp2 senv)))
      (quotient-exp (exp1 exp2) (quotient-exp (translation-of exp1 senv) (translation-of exp2 senv)))
      (bool-exp (bexp) (bool-exp (translation-of-bool-exp bexp senv)))
      (if-bool-exp (bexp exp1 exp2) (if-bool-exp (bool-exp (translation-of-bool-exp bexp senv))
                                                 (translation-of exp1 senv)
                                                 (translation-of exp2 senv)))
      (var-exp (var) (nameless-var-exp (apply-senv senv var)))
      (let-exp (vars exps body) (nameless-let-exp (translation-of-let exps senv)
                                                  (translation-of body (extend-multivars-senv vars senv))))
      (let*-exp (vars exps body)
                (nameless-let*-exp (translation-of-let* vars exps senv)
                                   (translation-of body (extend-multivars-senv vars senv))))
      (emptylist-exp () (emptylist-exp))
      (cons-exp (exp1 exp2) (cons-exp (translation-of exp1 senv) (translation-of exp2 senv)))
      (car-exp (exp) (car-exp (translation-of exp senv)))
      (cdr-exp (exp) (cdr-exp (translation-of exp senv)))
      (list-exp (exps) (list-exp (translation-of-exps exps senv)))
      (cond-exp (boolexps consequence-exps)
                (cond-exp (translation-of-boolexps boolexps senv)
                          (translation-of-exps consequence-exps senv)))
      (print-exp (exp)
                 (print-exp (translation-of exp senv)))
      (unpack-exp (vars exp1 body)
                  (nameless-unpack-exp (translation-of exp1 senv)
                                       (translation-of body (extend-multivars-senv vars senv))))
      (proc-exp (vars body)
                (nameless-proc-exp (translation-of body (extend-multivars-senv vars senv))))
      (call-exp (rator rands)
                (call-exp (translation-of rator senv)
                          (translation-of-exps rands senv)))
      (letproc-exp (proc-name vars proc-body body)
                   (nameless-letproc-exp (translation-of proc-body (extend-multivars-senv vars senv))
                                         (translation-of body (extend-senv proc-name senv))))
      ;;we are not able to process dynamic-binding-proc-exp,skip
      (dynamic-binding-proc-exp (vars body)
                                (eopl:error 'translation-of "dynamic-binding-proc-exp is not usable for lexical addressing"))
      (letrec-exp (proc-names procs-vars proc-bodys letrec-body)
                  (begin (eopl:printf "letrec-exp will be handled soon!")
                         exp))
      ;;skip for nameless exp
      (else
       (eopl:error 'translation-of "meets nameless exp"))

      )))


(define translation-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
                 (a-program (translation-of exp (init-senv)))))))

(provide translation-of-program)

(define run-translation
  (lambda (string)
    (translation-of-program (scan&parse string))))

(provide run-translation)

;;test for example from book
(run-translation "let x=37 in proc(y) let z=-(y,x) in -(x,y)")



;;;The Nameless Interpreter
(define nameless-environment?
  (lambda (x)
    ((list-of expval?) x)))

(define empty-nameless-env
  (lambda ()
    '()))

(define extend-nameless-env
  (lambda (val nameless-env)
    (cons val nameless-env)))

(define extend-multivals-nameless-env
  (lambda (vals nameless-env)
    (if (null? vals)
        nameless-env
        (cons (car vals) (extend-multivals-nameless-env (cdr vals) nameless-env)))))

(define apply-nameless-env
  (lambda (nameless-env n)
    (list-ref nameless-env n)))

(define-datatype nameless-proc nameless-proc?
  (nameless-procedure (body expression?)
                      (saved-nameless-environment nameless-environment?))
  (nameless-trace-procedure (body expression?)
                      (saved-nameless-environment nameless-environment?))
  )

(define apply-nameless-procedure
  (lambda (nameless-proc1 args)
    (cases nameless-proc nameless-proc1
      (nameless-procedure (body saved-nameless-env)
                          (nameless-value-of body (extend-multivals-nameless-env args saved-nameless-env)))
      (nameless-trace-procedure (body saved-nameless-env)
                                 (begin (eopl:printf "nameless:entering func")
                                 (newline)
                                 (let ((r (nameless-value-of body (extend-multivals-nameless-env args saved-nameless-env))))
                                    (begin (eopl:printf "nameless:exiting func")
                                       (newline)
                                       r))))
                                
      )))

(define init-nameless-env
  (lambda ()
    (extend-nameless-env
     (num-val 1)
     (extend-nameless-env (num-val 5)
                          (extend-nameless-env (num-val 10) (empty-nameless-env))))))

(define nameless-value-of-bool-exp
      (lambda (nameless-exp nameless-env)
        (define compare-operation
          (lambda (op exp1 exp2 nameless-env)
            (let ((val1 (nameless-value-of exp1 nameless-env))
                  (val2 (nameless-value-of exp2 nameless-env)))
              (bool-val (op (expval->num val1) (expval->num val2))))))
        (cases boolexpression nameless-exp
          (equal?-bool-exp (exp1 exp2)
                           (compare-operation eqv? exp1 exp2 nameless-env))
          (greater?-bool-exp (exp1 exp2)
                             (compare-operation > exp1 exp2 nameless-env))
          (less?-bool-exp (exp1 exp2)
                          (compare-operation < exp1 exp2 nameless-env))
          (zero?-bool-exp (exp)
                          (bool-val (zero? (expval->num (nameless-value-of exp nameless-env)))))
          (null?-bool-exp (exp)
                          (bool-val (null? (expval->list (nameless-value-of exp nameless-env))))))))

(define nameless-value-of
  (lambda (nameless-exp nameless-env)

     (define arithmetic-operation
      (lambda (op exp1 exp2 nameless-env)
        (let ((val1 (nameless-value-of exp1 nameless-env))
              (val2 (nameless-value-of exp2 nameless-env)))
          (num-val (op (expval->num val1) (expval->num val2))))))

     (define nameless-evaluate-let-exp
      (lambda (exps body-exp argenv finalenv)
        (if (null? exps)
            (nameless-value-of body-exp finalenv)
            (nameless-evaluate-let-exp
                              (cdr exps)
                              body-exp
                              argenv
                              (extend-nameless-env (nameless-value-of (car exps) argenv) finalenv)))))

     (define nameless-evaluate-let*-exp
      (lambda (exps body-exp env)
        (if (null? exps)
            (nameless-value-of body-exp env)
            (nameless-evaluate-let*-exp
                               (cdr exps)
                               body-exp
                               (extend-nameless-env (nameless-value-of (car exps) env) env)))))

     (define nameless-evaluate-list-exp
      (lambda (exps env)
        (if (null? exps)
            (list-val '())
            (list-val (cons (nameless-value-of (car exps) env)
                            (expval->list (nameless-evaluate-list-exp (cdr exps) env)))))))

     (define nameless-evaluate-cond-exp
      (lambda (preds cons env)
        (if (null? preds)
            (eopl:error 'value-of "none of the cond expression's test condition success")
            (if (expval->bool (nameless-value-of-bool-exp (car preds) env))
                (nameless-value-of (car cons) env)
                (nameless-evaluate-cond-exp (cdr preds) (cdr cons) env)))))

     (define evaluate-call-exp-rands
      (lambda (rands env)
        (if (null? rands)
            '()
            (cons (nameless-value-of (car rands) env)
                  (evaluate-call-exp-rands (cdr rands) env)))))
    
    (cases expression nameless-exp
      (const-exp (num) (num-val num))
      (minus-exp (exp) (num-val (- 0 (expval->num (nameless-value-of exp nameless-env)))))
      (nameless-var-exp (n) (apply-nameless-env nameless-env n))
      (diff-exp (exp1 exp2)
                (arithmetic-operation - exp1 exp2 nameless-env))
      
      (add-exp (exp1 exp2)
               (arithmetic-operation + exp1 exp2 nameless-env))
     
      (multiply-exp (exp1 exp2)
                    (arithmetic-operation * exp1 exp2 nameless-env))
      
      (quotient-exp (exp1 exp2)
                    (arithmetic-operation remainder exp1 exp2 nameless-env))
      
      (if-bool-exp (boolexp exp2 exp3)
             (if (expval->bool (nameless-value-of-bool-exp boolexp nameless-env))
                 (nameless-value-of exp2 nameless-env)
                 (nameless-value-of exp3 nameless-env)))

      (bool-exp (exp)
                (nameless-value-of-bool-exp exp nameless-env))
              
      (nameless-let-exp (exps body)
               (nameless-evaluate-let-exp exps body nameless-env nameless-env))

      (nameless-let*-exp (exps body)
               (nameless-evaluate-let*-exp exps body nameless-env))
                      
      (emptylist-exp () (list-val '()))
      (car-exp (exp)
               (let ((val (nameless-value-of exp nameless-env)))
                 (car (expval->list val))))
      (cdr-exp (exp)
               (let ((val (nameless-value-of exp nameless-env)))
                 (list-val (cdr (expval->list val)))))
      
      (cons-exp (exp1 exp2)
                (let ((val1 (nameless-value-of exp1 nameless-env))
                      (val2 (nameless-value-of exp2 nameless-env)))
                  (list-val (cons val1 (expval->list val2)))))
      (list-exp (exps)
                (nameless-evaluate-list-exp exps nameless-env))
      (cond-exp (preds consequences)
                (nameless-evaluate-cond-exp preds consequences nameless-env))
      (print-exp (exp)
                 (begin (eopl:printf "~s" (nameless-value-of exp nameless-env)) (num-val 1)))
      (nameless-unpack-exp (exp1 body)
                  (let ((vals (expval->list (nameless-value-of exp1 nameless-env))))
                        (nameless-value-of body (extend-multivals-nameless-env vals nameless-env))))
      (nameless-proc-exp (body)
                (nameless-proc-val (nameless-procedure body nameless-env)))
      (call-exp (rator rands)
                (apply-nameless-procedure (expval->nameless-proc (nameless-value-of rator nameless-env)) (evaluate-call-exp-rands rands nameless-env)))

      (nameless-letproc-exp (proc-body let-body)
                            (nameless-value-of let-body (extend-nameless-env (nameless-proc-val (nameless-procedure proc-body nameless-env)) nameless-env)))
      (nameless-traceproc-exp (body)
                              (nameless-proc-val (nameless-trace-procedure body nameless-env)))

     ;; (letrec-exp (p-names procs-vars p-bodys letrec-body)
     ;;             (nameless-value-of letrec-body (extend-env-rec p-names procs-vars p-bodys nameless-env)))

      ;;else case for  var-exp let-exp let*-exp
      ;;unpack-exp proc-exp letproc-exp traceproc-exp
      ;;dynamic-binding-proc-exp letrec-exp 
      (else
       (eopl:error 'nameless-value-of "not support exp:~s" nameless-exp))
      )))

(define nameless-value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
                 (nameless-value-of exp (init-nameless-env))))))
 


(define nameless-run
  (lambda (string)
    (nameless-value-of-program (run-translation string))))

(define testnp  "let x=37 in let f = proc(y) let z=-(y,x) in -(x,y) in (f 40)")


(nameless-run testnp)
      
      
      
  
          