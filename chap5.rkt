#lang eopl
(require "./chap2.rkt")
(require  "./chap2-from-section2.4-to-end.rkt")
(require rackunit)
(require racket/format)
(require racket/string)
;(require racket)

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
    (expression ("/" "(" expression "," expression ")") div-exp)
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
    (expression ("try" expression "catch" "(" identifier ")" expression) try-exp)
    (expression ("raise" expression) raise-exp)
    (expression ("resume" expression) resume-exp)
    
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
  (div-exp (exp1 expression?) (exp2 expression?))
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
  (try-exp (exp1 expression?) (var identifier?) (handler-exp expression?))
  (raise-exp (exp expression?))
  (resume-exp (exp expression?))


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
  (string-val (s string?))
  (cont-val (cont continuation?))
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
  (lambda (proc1 args env cont)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of/k body (extend-multivars-env vars args saved-env) cont))
      (dynamic-binding-procedure (vars body)
                 (value-of/k body (extend-multivars-env vars args env) cont)) ;;dynamic binding, evaluate the body with current environment.
      (trace-procedure (vars body saved-env)
                       (begin (eopl:printf "entering func")
                              (newline)
                              (value-of/k body (extend-multivars-env vars args saved-env) (trace-procedure-cont cont)))))))

(define check-procedure-signature
  (lambda (proc1 n)
    (define check-match
      (lambda (expect actual)
        (list (= expect actual) expect actual)))
    (cases proc proc1
      (procedure (vars body saved-env)
                 (check-match (length vars) n))
      (dynamic-binding-procedure (vars body)
                                 (check-match (length vars) n))
      (trace-procedure (vars body saved-env)
                       (check-match (length vars) n)))))
                                 
                 
                             

(define-datatype continuation continuation?
  (end-cont)
  (zero-cont (cont continuation?))
  (binary-operation-op1-cont (op (lambda (o) #t))
                        (exp2 expression?)
                        (env environment?)
                        (cont continuation?))
  (binary-operation-op2-cont (op (lambda (o) #t))
                        (val1 expval?)
                        (env environment?)
                        (cont continuation?))
  (compare-operation-op1-cont (op (lambda (o) #t))
                        (exp2 expression?)
                        (env environment?)
                        (cont continuation?))
  (compare-operation-op2-cont (op (lambda (o) #t))
                        (val1 expval?)
                        (env environment?)
                        (cont continuation?))

  (zero-bool-exp-cont (cont continuation?))
  (null-bool-exp-cont (cont continuation?))

  (if-exp-cont (exp2 expression?) (exp3 expression?) (env environment?) (cont continuation?))

  (let-binding-cont (var identifier?) (vars (list-of identifier?)) (exps (list-of expression?)) (body expression?) (argenv environment?) (finalenv environment?) (cont continuation?))

  (let*-binding-cont (var identifier?) (vars (list-of identifier?)) (exps (list-of expression?)) (body expression?) (env environment?) (cont continuation?))

  (car-exp-cont (cont continuation?))
  (cdr-exp-cont (cont continuation?))
  (cons-exp-op1-cont (exp2 expression?) (env environment?) (cont continuation?))
  (cons-exp-op2-cont (val1 expval?) (cont continuation?))

  (evaluate-list-exp-cont (listval expval?) (exps (list-of expression?)) (env environment?) (cont continuation?))

  (cond-exp-cont (con expression?) (preds (list-of boolexpression?)) (cons (list-of expression?)) (env environment?) (cont continuation?))
  (print-exp-cont (cont continuation?))
  (unpack-exp-cont (vars (list-of identifier?)) (body expression?) (env environment?) (cont continuation?))

  (rator-cont (exps (list-of expression?)) (env environment?) (cont continuation?))

  (evaluate-call-exp-rands-cont (proc expval?) (argvals (list-of expval?)) (rands (list-of expression?)) (env environment?) (cont continuation?))

  (begin-exp-cont (subexps (list-of expression?)) (env environment?) (cont continuation?))

  (newref-exp-cont (cont continuation?))

  (deref-exp-cont (cont continuation?))


  (setref-exp-op1-cont (exp2 expression?) (env environment?) (cont continuation?))
  (setref-exp-op2-cont (val1 expval?) (cont continuation?))

  (trace-procedure-cont (cont continuation?))

  (try-exp-cont (var identifier?) (handler-exp expression?) (env environment?) (cont continuation?))
  (raise-exp-cont (cont continuation?))
  (resume-exp-cont (cont continuation?))

  
  )

(define apply-cont
  (lambda (cont val)
    (lambda ()
    (cases continuation cont
      (end-cont ()
                ;;(eopl:error "End of Computation.~%" val))
                val)
      (zero-cont (cont) (apply-cont cont (num-val (- 0 (expval->num val)))))
      (binary-operation-op1-cont (op exp2 env cont)
                                (value-of/k exp2 env (binary-operation-op2-cont op val env cont)))
      
      (binary-operation-op2-cont (op val1 env cont)
                                 (if (and (eqv? op /) (zero? (expval->num val)))
                                     (apply-cont (raise-exp-cont cont) (string-val "try to divide by 0"))
                                     (apply-cont cont (num-val (op (expval->num val1) (expval->num val))))))
      
      (compare-operation-op1-cont (compare-op exp2 env cont)
                                  (value-of/k exp2 env (compare-operation-op2-cont compare-op val env cont)))
      
      (compare-operation-op2-cont (compare-op val1 env cont)
                                  (apply-cont cont (bool-val (compare-op (expval->num val1) (expval->num val)))))

      (zero-bool-exp-cont (cont)
                          (apply-cont cont (bool-val (zero? (expval->num val)))))

      (null-bool-exp-cont (cont)
                          (apply-cont cont (bool-val (null? (expval->list val)))))

      (if-exp-cont (exp2 exp3 env cont)
                   (if (expval->bool val)
                       (value-of/k exp2 env cont)
                       (value-of/k exp3 env cont)))

      (let-binding-cont (var vars exps body argenv finalenv cont)
                        (evaluate-let-exp/k
                         vars
                         exps
                         body
                         argenv
                         (extend-env var val finalenv)
                         cont))
      (let*-binding-cont (var vars exps body env cont)
                         (evaluate-let*-exp/k
                          vars
                          exps
                          body
                         (extend-env var val env)
                         cont))
      (car-exp-cont (cont)
                    (apply-cont cont (car (expval->list val))))

      (cdr-exp-cont (cont)
                    (apply-cont cont (list-val (cdr (expval->list val)))))
      (cons-exp-op1-cont (exp2 env cont)
                         (value-of/k exp2 env (cons-exp-op2-cont val cont)))
      (cons-exp-op2-cont (val1 cont)
                         (apply-cont cont (list-val (cons val1 (expval->list val)))))

      (evaluate-list-exp-cont (listval exps env cont)
                              (evaluate-list-exp/k (list-val (cons val (expval->list listval))) exps env cont))

      (cond-exp-cont (con preds cons env cont)
                     (if (expval->bool val)
                         (value-of/k con env cont)
                         (evaluate-cond-exp/k preds cons env cont)))
      (print-exp-cont (cont)
                      (begin (eopl:printf "~s" val) (num-val 1)))

      (unpack-exp-cont (vars body env cont)
                       (let ((vals (expval->list val)))
                         (if (not (eqv? (length vars) (length vals)))
                             (eopl:error 'unpack-exp "number of vars do not match the list element length in expression:~s" exp)
                        (value-of/k body (extend-multivars-env vars vals env) cont))))

      (rator-cont (rands env cont)
                  (letrec ((r (check-procedure-signature (expval->proc val) (length rands)))
                           (ok (car r))
                           (expect (cadr r))
                           (actual (caddr r)))
                    (if ok
                        (evaluate-call-exp-rands/k val '() (reverse rands) env cont)
                      ;;else raise exception
                        (apply-cont (raise-exp-cont cont) (string-val (string-append "Exception wrong number of arguments expect:" (~a expect) ",actual:"  (~a actual)))))))
                        ;;(value-of/k (raise-exp (const-exp -100000)) env cont))))
                        ;(eopl:error 'callfunc " a proce- dure is called with the wrong number of arguments expect:~s, actual:~s" expect actual))))

      (evaluate-call-exp-rands-cont (proc argvals rands env cont)
                                    (evaluate-call-exp-rands/k proc (cons val argvals) rands env cont))

      (begin-exp-cont (subexps env cont)
                      (evaluate-begin-subexps/k subexps val env cont))

      (newref-exp-cont (cont)
                       (apply-cont cont (newref val)))

      (deref-exp-cont (cont)
                      (apply-cont cont (deref val)))

      (setref-exp-op1-cont (exp2 env cont)
                           (value-of/k exp2 env (setref-exp-op2-cont val cont)))

      (setref-exp-op2-cont (refval cont)
                           (begin (setref! refval val)
                                  (apply-cont cont val)))

      (trace-procedure-cont (cont)
                            (begin (eopl:printf "exiting func")
                                       (newline)
                                       (apply-cont cont val)))

      (try-exp-cont (var handler-exp env cont)
                    (apply-cont cont val))

      (raise-exp-cont (cont)
                      (handle-exception cont val))
      (resume-exp-cont (cont)
                       (apply-cont cont val))
                        
      ))))

(define handle-exception
  (lambda (o-cont val)
    (define apply-handler
      (lambda ()

        (define report-uncaught-exception
          (lambda ()
            (eopl:error 'apply-handler "err: uncaught exception ~s " val )))

        (let ((try-cont (pop-from-exception-stack)))
          (if try-cont
              (cases continuation try-cont
                (try-exp-cont (var handler-exp env cont) (value-of/k handler-exp (extend-env '$ (cont-val o-cont) (extend-env var val env)) cont))
                (else (eopl:error 'apply-handler "not an try continuation: ~s" try-cont)))
              (report-uncaught-exception)))))
    (apply-handler)))


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

(define expval->cont
  (lambda (val)
    (cases expval val
      (cont-val (n) n)
      (else (eopl:error 'expval->cont "not a cont value.~s" val)))))


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


(define the-exception-stack #f)

(define empty-exception-stack
  (lambda ()
    (set! the-exception-stack '())))
(define push-to-exception-stack
  (lambda (cont)
    (set! the-exception-stack (cons cont the-exception-stack))))
(define pop-from-exception-stack
  (lambda ()
    (if (null? the-exception-stack)
        #f
        (let ((ele (top-of-exception-stack)))
          (begin (set! the-exception-stack (cdr the-exception-stack))
                 ele)))))

(define top-of-exception-stack
  (lambda ()
    (if (null? the-exception-stack)
        #f
        (car the-exception-stack))))
               

(define trampoline
  (lambda (bounce)
    (if (expval? bounce)
        bounce
        (trampoline (bounce)))))

(define value-of-program
  (lambda (prog)
    (cases program prog
      (a-program (exp)
                 (begin (initialize-store!)
                        (empty-exception-stack)
                 (trampoline (value-of/k exp (init-env) (end-cont))))))))

(define value-of-bool-exp/k
      (lambda (exp env cont)
        (define compare-operation
          (lambda (op exp1 exp2 env cont)
            (value-of/k exp1 env (compare-operation-op1-cont op exp2 env cont))))
        
        (cases boolexpression exp
          (equal?-bool-exp (exp1 exp2)
                           (compare-operation eqv? exp1 exp2 env cont))
          (greater?-bool-exp (exp1 exp2)
                             (compare-operation > exp1 exp2 env cont))
          (less?-bool-exp (exp1 exp2)
                          (compare-operation < exp1 exp2 env cont))
          (zero?-bool-exp (exp)
                          (value-of/k exp env (zero-bool-exp-cont cont)))
          (null?-bool-exp (exp)
                          (value-of/k exp env (null-bool-exp-cont cont))))))

    (define evaluate-let-exp/k
      (lambda (vars exps body-exp argenv finalenv cont)
        (if (null? vars)
            (value-of/k body-exp finalenv cont)
            (value-of/k (car exps) argenv (let-binding-cont (car vars) (cdr vars) (cdr exps) body-exp argenv finalenv cont)))))

    (define evaluate-let*-exp/k
      (lambda (vars exps body-exp env cont)
        (if (null? vars)
            (value-of/k body-exp env cont)
            (value-of/k (car exps) env (let*-binding-cont (car vars) (cdr vars) (cdr exps) body-exp env cont)))))

    (define evaluate-list-exp/k
      (lambda (listval exps env cont)
        (if (null? exps)
            (apply-cont cont listval)
            (value-of/k (car exps) env (evaluate-list-exp-cont listval (cdr exps) env cont)))))

    (define evaluate-cond-exp/k
      (lambda (preds cons env cont)
        (if (null? preds)
            (eopl:error 'value-of "none of the cond expression's test condition success")
            (value-of-bool-exp/k (car preds) env (cond-exp-cont (car cons) (cdr preds) (cdr cons) env cont)))))

    (define evaluate-call-exp-rands/k
      (lambda (procval argvals rands env cont)
        (if (null? rands)
            (apply-procedure (expval->proc procval) argvals env cont)
            (value-of/k (car rands) env (evaluate-call-exp-rands-cont procval argvals (cdr rands) env cont)))))

    (define evaluate-begin-subexps/k 
      (lambda (subexps pre-val env cont)
        (if (null? subexps)
            (apply-cont cont pre-val)
            (value-of/k (car subexps) env (begin-exp-cont (cdr subexps) env cont)))))

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

(define value-of/k
  (lambda (exp env cont)
    (define arithmetic-operation
      (lambda (op exp1 exp2 env cont)
        (value-of/k exp1 env (binary-operation-op1-cont op exp2 env cont))))

    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (minus-exp (exp) (value-of/k exp env (zero-cont cont)))
      (var-exp (var) (apply-cont cont (apply-env env var)))
      (diff-exp (exp1 exp2)
                (arithmetic-operation - exp1 exp2 env cont))
      
      (add-exp (exp1 exp2)
               (arithmetic-operation + exp1 exp2 env cont))
     
      (multiply-exp (exp1 exp2)
                    (arithmetic-operation * exp1 exp2 env cont))
      (div-exp (exp1 exp2)
               (arithmetic-operation / exp1 exp2 env cont))

      
      (quotient-exp (exp1 exp2)
                    (arithmetic-operation remainder exp1 exp2 env cont))
      
      (if-bool-exp (boolexp exp2 exp3)
             (value-of-bool-exp/k boolexp env (if-exp-cont exp2 exp3 env cont)))

      (bool-exp (exp)
                (value-of-bool-exp/k exp env cont))
              
      (let-exp (vars exps body)
               (evaluate-let-exp/k vars exps body env env cont))

      (let*-exp (vars exps body)
                (evaluate-let*-exp/k vars exps body env cont))
      
      (emptylist-exp () (apply-cont cont (list-val '())))
      
      (car-exp (exp)
               (value-of/k exp env (car-exp-cont cont)))
              
      (cdr-exp (exp)
               (value-of/k exp env (cdr-exp-cont cont)))
      
      (cons-exp (exp1 exp2)
                (value-of/k exp1 env (cons-exp-op1-cont exp2 env cont)))
              
      (list-exp (exps)
                (evaluate-list-exp/k (list-val '()) (reverse exps) env cont))
      (cond-exp (preds consequences)
                (evaluate-cond-exp/k preds consequences env cont))
      (print-exp (exp)
                 (value-of/k exp env (print-exp-cont cont)))
      (unpack-exp (vars exp1 body)
                  (value-of/k exp1 env (unpack-exp-cont vars body env cont)))
              
      (proc-exp (vars body)
                (apply-cont cont (proc-val (procedure vars body env))))
      (call-exp (rator rands)
                (value-of/k rator env (rator-cont rands env cont)))

      (letproc-exp (proc-name vars proc-body body)
                   (value-of/k body (extend-env proc-name (proc-val (procedure vars proc-body env)) env) cont))
      (traceproc-exp (vars body)
                     (apply-cont cont (proc-val (trace-procedure vars body env))))
      (dynamic-binding-proc-exp (vars body)
                                (apply-cont cont (proc-val (dynamic-binding-procedure vars body))))
      (letrec-exp (p-names procs-vars p-bodys letrec-body)
                  (value-of/k letrec-body (extend-env-rec p-names procs-vars p-bodys env) cont))

      (begin-exp (exp1 subexps)
                 (value-of/k exp1 env (begin-exp-cont subexps env cont)))

      (newref-exp (exp)
                  (value-of/k exp env (newref-exp-cont cont)))

      (deref-exp (exp)
                 (value-of/k exp env (deref-exp-cont cont)))

      (setref-exp (exp1 exp2)
                  (value-of/k exp1 env (setref-exp-op1-cont exp2 env cont)))

      (try-exp (exp1 var handler-exp)
               (let ((try-cont (try-exp-cont var handler-exp env cont)))
                 (begin (push-to-exception-stack try-cont)
                        (value-of/k exp1 env try-cont))))

      (raise-exp (exp1)
                 (value-of/k exp1 env (raise-exp-cont cont)))
 
      (resume-exp (exp1)
                  (value-of/k exp1 env (resume-exp-cont (expval->cont (apply-env env '$)))))
      
      ;;lexical addressing; any occurence of the nameless expression we'll report an error
      (else
       (eopl:error 'value-of "occurence of nameless exp:~s" exp))

      )))

(define scan&parse
    (sllgen:make-string-parser lexical-spec grammer-spec))



(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(define testp "let x = 1 in if zero?(-(x,i)) then 10 else 100")

;;test for exercise3.6
(check-equal? (run " minus(-(minus(5),9))") (num-val 14))

;;test for exercise3.7
(check-equal? (run "+(//(13,4),*(minus(3), 2))") (num-val -5))

;;test for exercise3.8
(check-equal? (run "equal?(//(13,4),minus(minus(1)))") (bool-val #t))
(check-equal? (run "equal?(//(minus(13),4),minus(minus(1)))") (bool-val #f))

(check-equal? (run "greater?(//(13,4),minus(2))") (bool-val #t))
(check-equal? (run "less?(//(13,4),minus(2))") (bool-val #f))
(check-equal? (run "greater?(//(13,minus(4)),2)") (bool-val #f))
(check-equal? (run "less?(//(13,minus(4)),2)") (bool-val #t))

;;test for exercise3.9
;;test for cons
(check-equal? (run "let x = 4 in cons(x,cons(cons(-(x,1),emptylist),emptylist))") (list-val (cons (num-val 4)
                                                                                                  (list (list-val (cons (num-val 3) '()))))))

;;test for car 
(check-equal? (run "let y = let x = 4 in cons(x,cons(cons(-(x,1),emptylist),emptylist)) in car(y)") (num-val 4))

;;test for cdr
(check-equal? (run "let y = let x = 4 in cons(x,cons(cons(-(x,1),emptylist),emptylist)) in cdr(y)") (list-val (list (list-val (list (num-val 3))))))

;;test for null?
(check-equal? (run "null?(cons(1,emptylist))") (bool-val #f))
(check-equal? (run "null?(emptylist)") (bool-val #t))

;;test for exercise3.10
(check-equal? (run "let x = 4 in list(x,-(x,1),-(x,3))") (list-val (list (num-val 4) (num-val 3) (num-val 1))))

;;test for exercise3.12
(check-equal? (run "cond { zero?(1) ==> 1
             greater?(2,3) ==> 2
             less?(3,1) ==> 3
             null?(emptylist) ==> 4
             greater?(3,1) ==> 5 } end ") (num-val 4))


(check-equal? (run "if equal?(1,1) then 1 else 2") (num-val 1))

;;test for exercise3.15
(check-equal? (run "let a = 1 in print(let b = 1 in cond {
                                    zero?(a) ==> 0
                                    greater?(a,i) ==> 1
                                    zero?(-(a,i)) ==> 2
                                    } end )") (num-val 1))

;;test for exercise3.16
(check-equal? (run "let x = 30 in let x = -(x,1) y = -(x,2) in -(x,y)") (num-val 1))
(check-equal? (run "let x = 30 in let a = let x = -(x,1) y = -(x,2) in -(x,y) b = 2 in -(a,b)") (num-val -1))



;;test for exercise 3.17
(check-equal? (run "let x = 30 in let* x= -(x,1) y = -(x,2) in -(x,y)") (num-val 2))
(check-equal? (run "let x = 30 in let* a = let x = -(x,1) y = -(x,2) in -(x,y) b = 2 in -(a,b)") (num-val -1))


;;test for exercise3.18
(check-equal? (run "let u = 7 in unpack x y = cons(u,cons(3,emptylist)) in -(x,y)") (num-val 4))

;;test for basiec PROC Language
(check-equal? (run "let f = proc(x) -(x,1) in (f (f 77))") (num-val 75))
(check-equal? (run "let x = 200
      in let f = proc (z) -(z,x)
         in let x = 100
            in let g = proc (z) -(z,x)
               in -((f 1), (g 1))") (num-val -100))

(check-equal? (run "letproc f (x) -(x,1) in (f (f 77))") (num-val 75))

;;exercise 3.20
(check-equal? (run "let f = proc (x) proc (y) +(x,y) in ((f 3) 4)") (num-val 7))


;;test for exercise 3.21
(check-equal? (run "let f = proc (x,y,z) proc (u) +(u,+(x,+(y,z))) in
((f 1 2 3) 4)") (num-val 10))

(check-equal? (run "letproc f (x,y,z) +(x,+(y,z)) in (f 1 2 3)") (num-val 6))

;;exercise3.23
(check-equal? (run "let makemult = proc (maker) proc (x)
if zero?(x)
then 0
else -(((maker maker) -(x,1)), minus(4))
in let timesfour = proc (x) ((makemult makemult) x) in (timesfour 3)") (num-val 12))

(check-equal? (run "let makemultn = proc (n)
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
                               in (fact 10 fact)") (num-val 3628800))
                             
(define fact
  (lambda (n)
    (if (zero? n)
        1
        (* n (fact (- n 1))))))

;;; the trick Currying is used to support multiple params func.
;;; if we do not support multiple params func in our language grammer we can use Currying to achieve the same effect.

;;test for exercise 3.27
(check-equal? (run "let f = traceproc (x) traceproc (y) +(x,y) in ((f 3) 4)") (num-val 7))
(check-equal? (run "let f = traceproc (x,g) +(1,(g x))
 g = traceproc(y) y in
 (f 2 g)") (num-val 3))

    
(check-equal? (run " let a = 3
      in let p = dynamicproc (x) -(x,a)
a=5
in -(a,(p 2))") (num-val 8))

(check-equal? (run "let a = 3
      in let p = dynamicproc (z) a
         in let f = dynamicproc (x) (p 0)
            in let a = 5
in (f 2)") (num-val 5))

;;;section3.4 LETREC Language

                 
(check-equal? (run "letrec double(x) = if zero?(x) then 0 else +((double -(x,1)), 2) in (double 6)") (num-val 12))

;;test for exercise3.31
(check-equal? (run "letrec double(x,y) = if zero?(x) then 0 else +(y,+((double -(x,1) y), 2)) in (double 6 2)") (num-val 24))


;;test for exercise 3.32/3.33
(check-equal? (run "letrec
even(x) = if zero?(x) then 1 else (odd -(x,1))
odd(x) = if zero?(x) then 0 else (even -(x,1))
in (odd 12)") (num-val 0))

;;exercise 3.37
;;for test
(check-equal? (run "let fact = proc (n) +(n,1) in let fact = proc (n)
                          if zero?(n)
                          then 1
                          else *(n,(fact -(n,1)))
in (fact 5)") (num-val 25))

(check-equal? (run "let fact = dynamicproc (n) +(n,1) in let fact = dynamicproc (n)
                          if zero?(n)
                          then 1
                          else *(n,(fact -(n,1))) in (fact 6)") (num-val 720))
;;implement 3.37
(check-equal? (run
 " let even = dynamicproc(x) if zero?(x) then 1 else (odd -(x,1))
    in let odd = dynamicproc(x) if zero?(x) then 0 else (even -(x,1))
       in (odd 13)") (num-val 1))

;;testcase

(check-equal? (run "begin 3 end") (num-val 3))
(check-equal? (run "let x = 3
                     in begin -(x,1);+(x,1) end") (num-val 4))


(define testp1 "let x = newref(0)
                  in letrec even() = if zero?(deref(x)) then 1 else begin setref(x, -(deref(x), 1)); (odd) end
                            odd() = if zero?(deref(x)) then 0 else begin setref(x,-(deref(x),1)); (even) end
                      in begin setref(x,13); (even) end ")


(check-equal? (run testp1) (num-val 0))
(check-equal? (run "let x = newref(0)
       in begin setref(x,12); deref(x) end") (num-val 12))

(check-equal? (run " let x = newref(newref(0))
      in begin
          setref(deref(x), 11);
          deref(deref(x))
         end") (num-val 11))

(check-equal? (run "let g = let counter = newref(0) in proc (dummy)
begin
setref(counter, +(deref(counter), 1)); deref(counter)
                  end
      in let a = (g 11)
         in let b = (g 11)
            in -(a,b)") (num-val -1))

;;;section 5.3 imperative language is too easy to understand .

;;test for Exception
;(run "raise 100")
(check-equal? (run "let index
           = proc (n)
              letrec inner (lst)
               = if null?(lst)
                 then raise 99
                 else if zero?(-(car(lst),n))
                      then 0
else +((inner cdr(lst)), 1) in proc (lst)
try (inner lst) catch (x) resume x in ((index 5) list(2, 3))") (num-val 101))

(check-equal? (run "let index
           = proc (n)
              letrec inner (lst)
               = if null?(lst)
                 then raise 99
                 else if zero?(-(car(lst),n))
                      then 0
else +((inner cdr(lst)), 1) in proc (lst)
try (inner lst) catch (x) x in ((index 5) list(2, 3))") (num-val 99))

(check-equal? (run "let index
           = proc (n)
              letrec inner (lst)
               = if null?(lst)
                 then raise 99
                 else if zero?(-(car(lst),n))
                      then 0
else +((inner cdr(lst)), 1) in proc (lst)
try (inner lst) catch (x) x in ((index 5) list(2, 3, 5))") (num-val 2))

(check-equal? (run "try +(1,raise 100) catch(x) 199") (num-val 199))
(check-equal? (run "try +(1,raise 100) catch(x) resume 199") (num-val 200))


(run " try let f = proc(n,m)
                +(n,m)
         in (f 1 ) catch(x) x ")

;;test for exercise5.38
(check-equal? (run "/(6,2)") (num-val 3))
;(run "/(1,0)")
