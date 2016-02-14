#lang eopl

(require "./chap2.rkt")
(require  "./chap2-from-section2.4-to-end.rkt")
(require rackunit)


(define lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)))

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
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
    (expression ("newref" "(" expression ")") newref-exp)
    (expression ("deref" "(" expression ")") deref-exp)
    (expression ("setref" "(" expression "," expression ")") setref-exp)
    
    (boolexpression ("equal?" "(" expression "," expression ")") equal?-bool-exp)
    (boolexpression ("zero?" "(" expression ")") zero?-bool-exp)
    (boolexpression ("greater?" "(" expression "," expression ")") greater?-bool-exp)
    (boolexpression ("less?" "(" expression "," expression ")") less?-bool-exp)
    (boolexpression ("null?" "(" expression ")") null?-bool-exp)
    
    ))

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

(define extend-multivars-env
                      (lambda (vars vals env)
                        (if (null? vars)
                            env
                            (extend-env (car vars)
                                        (car vals)
                                        (extend-multivars-env (cdr vars) (cdr vals) env)))))

(define apply-env
  (lambda (env search-var)
     (define apply-env-mutually-rec
        (lambda (search-var p-names procs-vars p-bodys saved-env env)
          (if (null? p-names)
              (apply-env saved-env search-var)
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
  (if-bool-exp (bexp boolexpression?) (exp2 expression?) (exp3 expression?))
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
  (begin-exp (exp expression?) (subexps (list-of expression?)))
  (newref-exp (exp expression?))
  (deref-exp (exp expression?))
  (setref-exp (exp1 expression?) (exp2 expression?))

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

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (list-val (list (list-of expval?)))
  (proc-val (proc proc?))
  (ref-val (n integer?))
  )

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

(define expval->ref
  (lambda (val)
    (cases expval val
      (ref-val (n) n)
      (else (eopl:error 'expval->ref "not a ref value.~s" val)))))


(define init-env
  (lambda ()
    (extend-env 'i (num-val 1)
                (extend-env 'v (num-val 5)
                            (extend-env 'x (num-val 10)
                                        (empty-env))))))
(define the-store #f)
(define slots-size 10240)
(define latest-avaiable-slot #f)

(define empty-store
  (lambda ()
    (begin (set! latest-avaiable-slot 0)
           (make-vector slots-size #f))))
    

(define get-store
  (lambda ()
    the-store))

(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

(define get-latest-avaiable-slot
  (lambda ()
    (if (>= latest-avaiable-slot slots-size)
        (eopl:error 'get-latest-avaiable-slot "total slots:~s;current-avaiable-slot:~s" slots-size latest-avaiable-slot)
        latest-avaiable-slot)))

(define update-latest-avaiable-slot
  (lambda ()
    (set! latest-avaiable-slot (+ latest-avaiable-slot 1))))

(define value-of-program
  (lambda (prog)
    (cases program prog
      (a-program (exp)
                 (begin (initialize-store!)
                 (value-of exp (init-env)))))))

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

    (define evaluate-begin-subexps
      (lambda (subexps pre-val env)
        (if (null? subexps)
            pre-val
            (let ((val (value-of (car subexps) env)))
              (evaluate-begin-subexps (cdr subexps) val env)))))

    (define newref
      (lambda (expval)
        (let ((i (get-latest-avaiable-slot)))
          (begin (vector-set! the-store i expval)
                 (update-latest-avaiable-slot)
                 (ref-val i)))))

    (define deref
      (lambda (refval)
        (let ((i (expval->ref refval)))
          (vector-ref the-store i))))

    (define setref!
      (lambda (refval expval)
        (let ((i (expval->ref refval)))
          (begin (vector-set! the-store i expval)))))
              

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

      (begin-exp (exp1 subexps)
                 (let ((val (value-of exp1 env)))
                   (evaluate-begin-subexps subexps val env)))

      (newref-exp (exp)
                  (let ((val (value-of exp env)))
                    (newref val)))

      (deref-exp (exp)
                 (deref (value-of exp env)))

      (setref-exp (exp1 exp2)
                  (let ((refval (value-of exp1 env))
                        (expval (value-of exp2 env)))
                    (begin (setref! refval expval))
                           expval))
      
      ;;lexical addressing; any occurence of the nameless expression we'll report an error
      (else
       (eopl:error 'value-of "occurence of nameless exp:~s" exp))

      )))

(define scan&parse
    (sllgen:make-string-parser lexical-spec grammer-spec))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))