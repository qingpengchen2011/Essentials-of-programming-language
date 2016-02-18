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
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp) ;;let的语意是直接做一个variable的binding. not-mutable
    (expression ("letmutable" (arbno identifier "=" expression) "in" expression) letmutable-exp);;letmutable的语意是introduce一个reference; mutable. 当其作为函数参数时，可在函数内被修改且修改反应到原变量.
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("letref" (arbno identifier "=" expression) "in" expression) letref-exp) ;;letref语意同letmutable
    (expression ("lazylet" (arbno identifier "=" expression) "in" expression) lazylet-exp) 
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
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("setdynamic" identifier "=" expression "during" expression) setdynamic-exp)
    (expression ("pair" "(" expression "," expression ")") newpair-exp)
    (expression ("left" "(" expression ")") left-exp)
    (expression ("right" "(" expression ")") right-exp)
    (expression ("setleft" "(" expression "," expression ")") setleft-exp)
    (expression ("setright" "(" expression "," expression ")" ) setright-exp)
    (expression ("newarray" "(" expression "," expression ")") newarray-exp)
    (expression ("arrayref" "(" expression "," expression ")") arrayref-exp)
    (expression ("arrayset" "(" expression "," expression "," expression ")") arrayset-exp)
    (expression ("arraylength" "(" expression ")") arraylen-exp)
    
    
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
                  (newref (proc-val (procedure (car procs-vars) (car p-bodys) env)))
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
  (letmutable-exp (vars (list-of identifier?)) (exps (list-of expression?)) (body expression?))
  (letref-exp (vars (list-of identifier?)) (exps (list-of expression?)) (body expression?))
  (let*-exp (vars (list-of identifier?)) (exps (list-of expression?)) (body expression?))
  (lazylet-exp (vars (list-of identifier?)) (exps (list-of expression?)) (body expression?))
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
  (assign-exp (var identifier?) (exp expression?))
  (setdynamic-exp (var identifier?) (exp1 expression?) (exp2 expression?))
  (newpair-exp (exp1 expression?) (exp2 expression?))
  (left-exp (exp expression?))
  (right-exp (exp expression?))
  (setleft-exp (exp1 expression?) (exp2 expression?))
  (setright-exp (exp1 expression?) (exp2 expression?))
  (newarray-exp (exp1 expression?) (exp2 expression?))
  (arrayref-exp (exp1 expression?) (exp2 expression?))
  (arrayset-exp (exp1 expression?) (exp2 expression?) (exp3 expression?))
  (arraylen-exp (exp expression?))



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
  (mutpair-val (pair mutpair?))
  (array-val (ary array?))
  )

(define-datatype mutpair mutpair?
  (a-pair (ref reference?)))

(define-datatype array array?
  (a-array (start-ref reference?) (length integer?))
  (empty-array )
  )

(define-datatype thunk thunk?
  (a-thunk (exp expression?) (env environment?)))

(define reference?
  (lambda (val)
    (cases expval val
      (ref-val (n) #t)
      (else #f))))

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

(define expval->mutpair
  (lambda (val)
    (cases expval val
      (mutpair-val (pair) pair)
      (else (eopl:error 'expval->mutpair "not a mutpair value.~s" val)))))

(define expval->array
  (lambda (val)
    (cases expval val
      (array-val (ary) ary)
      (else (eopl:error 'expval->array "not a array value.~s" val)))))


(define init-env
  (lambda ()
    (extend-env 'i (newref (num-val 1))
                (extend-env 'v (newref (num-val 5))
                            (extend-env 'x (newref (num-val 10))
                                        (empty-env))))))
(define the-store #f)
(define slots-size 20480)
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

(define update-latest-avaiable-slot-by
  (lambda (step)
    (set! latest-avaiable-slot (+ latest-avaiable-slot step))))

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

(define new-pair
  (lambda (val1 val2)
    (let ((ref (newref val1)))
      (begin (newref val2)
             (a-pair ref)))))

(define left
  (lambda (pair)
    (cases mutpair pair
      (a-pair (ref)
              (deref ref)))))

(define right
  (lambda (pair)
    (cases mutpair pair
      (a-pair (ref)
              (let ((right-ref (ref-val (+ (expval->ref ref) 1))))
                (deref right-ref))))))

(define setleft
  (lambda (pair val)
    (cases mutpair pair
      (a-pair (ref)
              (setref! ref val)))))

(define setright
  (lambda (pair val)
    (cases mutpair pair
      (a-pair (ref)
              (let ((right-ref (ref-val (+ (expval->ref ref) 1))))
                (setref! right-ref val))))))

(define newarray
  (lambda (length init-val)
    (define alloc-space
      (lambda (size val)
        (if (zero? size)
            #t
            (begin (newref val)
                   (alloc-space (- size 1) val)))))
    (if (zero? length)
        (empty-array)
        (let ((start-ref (newref init-val)))
          (begin (alloc-space (- length 1) init-val)
                 (a-array start-ref length))))))
          

(define arrayref
  (lambda (ary index)
    (cases array ary
      (empty-array () (eopl:error 'arrayref "try to index an empty array with index:~s" index))
      (a-array (start-ref len)
               (if (>= index len)
                   (eopl:error 'arrayref "index out of range with array length:~s, but try to index at ~s" len index)
                   (let ((target-ref (ref-val (+ (expval->ref start-ref) index))))
                     (deref target-ref)))))))

(define arrayref-oprand
  (lambda (ary index)
    (cases array ary
      (empty-array () (eopl:error 'arrayref-oprand "try to index an empty array with index:~s" index))
      (a-array (start-ref len)
               (if (>= index len)
                   (eopl:error 'arrayref-oprand "index out of range with array length:~s, but try to index at ~s" len index)
                   (ref-val (+ (expval->ref start-ref) index)))))))
          
                  
(define arrayset
  (lambda (ary index val)
    (cases array ary
      (empty-array () (eopl:error 'arrayset "try to set an empty array."))
      (a-array (start-ref len)
               (if (>= index len)
                   (eopl:error 'arrayset "index out of range with array length:~s, but try to set at index: ~s" len index)
                   (let ((target-ref (ref-val (+ (expval->ref start-ref) index))))
                     (setref! target-ref val)))))))


(define arraylen
  (lambda (ary)
    (cases array ary
      (empty-array () (num-val 0))
      (a-array (start-ref len)
               (num-val len)))))


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

     (define evaluate-lazylet-exp
      (lambda (vars exps body-exp argenv finalenv)
        (if (null? vars)
            (value-of body-exp finalenv)
            (evaluate-lazylet-exp (cdr vars)
                              (cdr exps)
                              body-exp
                              argenv
                              (extend-env (car vars) (newref (a-thunk (car exps) argenv)) finalenv)))))

   

    (define evaluate-letmutable-exp
      (lambda (vars exps body-exp argenv finalenv)
        (if (null? vars)
            (value-of body-exp finalenv)
            (evaluate-letmutable-exp (cdr vars)
                              (cdr exps)
                              body-exp
                              argenv
                              (extend-env (car vars) (newref (value-of (car exps) argenv)) finalenv)))))

    (define evaluate-let*-exp
      (lambda (vars exps body-exp env)
        (if (null? vars)
            (value-of body-exp env)
            (evaluate-let*-exp (cdr vars)
                               (cdr exps)
                               body-exp
                               (extend-env (car vars) (newref (value-of (car exps) env)) env)))))

    (define evaluate-call-exp-rands
      (lambda (rands env)
        (if (null? rands)
            '()
            (cons
             (let ((rand (car rands)))
               (cases expression rand
                 (var-exp (var) (let ((ref (apply-env env var)))
                                  (if (reference? ref)
                                      ref
                                      (newref ref)))) ;;forward compatible. if the var is a expval, introduce a newref to it.
                 (arrayref-exp (exp1 exp2)
                               (let ((arrayval (value-of exp1 env))
                                     (indexval (value-of exp2 env)))
                                 (arrayref-oprand (expval->array arrayval) (expval->num indexval))))
                 (const-exp (n) (newref (num-val n)))

                 (proc-exp (vars body) (newref (proc-val (procedure vars body env))))
                 
                 (else (newref (a-thunk rand env))))) ;;for lazy evaluate.
             (evaluate-call-exp-rands (cdr rands) env)))))
                    
    (define evaluate-begin-subexps
      (lambda (subexps pre-val env)
        (if (null? subexps)
            pre-val
            (let ((val (value-of (car subexps) env)))
              (evaluate-begin-subexps (cdr subexps) val env)))))

    (define evaluate-thunk
      (lambda (thk)
        (cases thunk thk
          (a-thunk (exp env)
                   (value-of exp env)))))

    (cases expression exp
      (const-exp (num) (num-val num))
      (minus-exp (exp) (num-val (- 0 (expval->num (value-of exp env)))))
      (var-exp (var) (let ((stored-val (apply-env env var)))
                       (if (reference? stored-val)
                           (let ((val (deref stored-val)))
                             (if (thunk? val)
                                 (let ((thunk-val (evaluate-thunk val)))
                                   (begin (setref! stored-val thunk-val)  ;;memorize the thunk value.
                                          thunk-val))
                                 val))
                           stored-val)))
               
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

      (letmutable-exp (vars exps body)
               (evaluate-letmutable-exp vars exps body env env))

      (letref-exp (vars exps body)
                  (evaluate-letmutable-exp vars exps body env env))

      (let*-exp (vars exps body)
                (evaluate-let*-exp vars exps body env))

      (lazylet-exp (vars exps body)
               (evaluate-lazylet-exp vars exps body env env))
            
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
                        (value-of body (extend-multivars-env vars (map (lambda (val) (newref val)) vals) env)))))
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      (call-exp (rator rands)
                (apply-procedure (expval->proc (value-of rator env)) (evaluate-call-exp-rands rands env) env))
      (letproc-exp (proc-name vars proc-body body)
                   (value-of body (extend-env proc-name (newref (proc-val (procedure vars proc-body env))) env)))
      (traceproc-exp (vars body)
                     (proc-val (trace-procedure vars body env)))
      (dynamic-binding-proc-exp (vars body)
                                (proc-val (dynamic-binding-procedure vars body)))
      (letrec-exp (p-names procs-vars p-bodys letrec-body)
                  (value-of letrec-body (extend-env-rec p-names procs-vars p-bodys env)))

      (begin-exp (exp1 subexps)
                 (let ((val (value-of exp1 env)))
                   (evaluate-begin-subexps subexps val env)))
      (assign-exp (var exp)
                  (let ((val (value-of exp env))
                        (ref?? (apply-env env var)))
                    (if (reference? ref??)
                        (begin (setref! ref?? val)
                               (num-val 27))
                        (eopl:error 'assign-exp "try to set to a none ref variable:~s" var))))

      (setdynamic-exp (var exp body)
                      (letrec ((new-val (value-of exp env))
                               (var-ref (apply-env env var))
                               (old-val (deref var-ref)))
                        (begin (setref! var-ref new-val)
                               (let ((new-val (value-of body env)))
                                 (begin (setref! var-ref old-val)
                                        new-val)))))

      (newpair-exp (exp1 exp2)
                   (let ((val1 (value-of exp1 env))
                         (val2 (value-of exp2 env)))
                     (mutpair-val (new-pair val1 val2))))

      (left-exp (exp)
                (let ((val (value-of exp env)))
                  (left (expval->mutpair val))))

      (right-exp (exp)
                 (let ((val (value-of exp env)))
                   (right (expval->mutpair val))))

      (setleft-exp (exp1 exp2)
                   (let ((val1 (value-of exp1 env))
                         (val2 (value-of exp2 env)))
                     (begin (setleft (expval->mutpair val1) val2)
                            (num-val 82))))

      (setright-exp (exp1 exp2)
                    (let ((val1 (value-of exp1 env))
                          (val2 (value-of exp2 env)))
                      (begin (setright (expval->mutpair val1) val2)
                             (num-val 83))))

      (newarray-exp (exp1 exp2)
                    (let ((size-val (value-of exp1 env))
                          (initval-val (value-of exp2 env)))
                      (array-val (newarray (expval->num size-val) initval-val))))
      (arrayref-exp (exp1 exp2)
                    (let ((arrayval (value-of exp1 env))
                          (indexval (value-of exp2 env)))
                      (arrayref (expval->array arrayval) (expval->num indexval))))
      (arrayset-exp (exp1 exp2 exp3)
                    (let ((arrayval (value-of exp1 env))
                          (indexval (value-of exp2 env))
                          (valtobeset (value-of exp3 env)))
                      (begin (arrayset (expval->array arrayval) (expval->num indexval) valtobeset)
                             (num-val 100))))
      (arraylen-exp (exp)
                    (let ((arrayval (value-of exp env)))
                      (arraylen (expval->array arrayval))))
                   
                        
       ;;lexical addressing; any occurence of the nameless expression we'll report an error
      (else
       (eopl:error 'value-of "occurence of nameless exp:~s" exp))

      )))

(define scan&parse
    (sllgen:make-string-parser lexical-spec grammer-spec))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))


;;---------------------------------
;;old test case copied

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


#|
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
|#
                             
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

;;---------------
;;test var-exp
(check-equal? (run "let x = 1 in x") (num-val 1))

;;test let
(check-equal? (run "let x = 1 in let y = 2 in +(x,y)") (num-val 3))

;;test letrec and set
(check-equal? (run "  letmutable x = 0
             in letrec even()
                        = if zero?(x)
                          then 1
                          else begin
                                set x = -(x,1);
(odd ) end
                       odd()
                        = if zero?(x)
                          then 0
                          else begin
                                set x = -(x,1);
                                (even )
                               end
in begin set x = 13; (odd ) end") (num-val 1))

;;test proc and set
(check-equal? (run "let g = letmutable count = 0
                     in proc (dummy)
                         begin
                          set count = +(count,1);
                          count
                         end
             in let a = (g 11)
                in let b = (g 11)
                   in -(b,a)")  (num-val 1))

;;exercise 4.16
(check-equal? (run "letmutable times4 = 0
       in begin set times4 = proc (x)
            if zero?(x) then 0 else +((times4 -(x,1)),4); (times4 3) end ") (num-val 12))

;;test for exercise 4.20
(check-equal? (run "letmutable x = 1 y = 2 in begin set x = 10; set y = 20;  +(x,y) end ") (num-val 30))

;;test for exercise4.21
(check-equal? (run "letmutable x = 11 in let p = proc(y) -(y,x) in -(setdynamic x = 17 during (p 22), (p 13))") (num-val 3))

;;Mutable-pair test
(check-equal? (run  "let glo = pair(11,22)
in let f = proc (loc)
let d1 = setright(loc, left(loc)) in let d2 = setleft(glo, 99)
in -(left(loc),right(loc))
in (f glo)") (num-val 88))

(check-equal? (run "let p = pair(1,2) in
              let f = proc (p) begin setright(p,10);setleft(p,100) end
               in begin (f p); -(left(p),right(p)) end") (num-val 90))

;;test for exercise4.29
(check-equal? (run "
      let a = newarray(2,minus(99))
          p = proc (x)
               let v = arrayref(x,1)
in arrayset(x,1,+(v,1))
in begin arrayset(a,1,0); (p a); (p a); arrayref(a,1) end") (num-val 2))

;;error test
#|
(check-equal? (run "
      let a = newarray(0,minus(99))
          p = proc (x)
               let v = arrayref(x,1)
in arrayset(x,1,+(v,1))
in begin  arrayref(a,1) end") (num-val 2))
|#

;;test for exercise4.30
(check-equal? (run "arraylength(newarray(2,99))") (num-val 2))
(check-equal? (run "arraylength(newarray(0,100))") (num-val 0))

;;test for Parameter-Passing Variations
(check-equal? (run "let u = 7 in unpack x y = cons(u,cons(3,emptylist)) in begin set x = 100; set y = 200; +(x,y) end ") (num-val 300))
;;note:我们改变了语意，只有是letmutable的变量才是mutable的.
(check-equal? (run "letmutable y = 10 in let f = proc(x) begin set x = 100 end in begin (f y); y end") (num-val 100))

;;tests for call-by-reference
(check-equal? (run " let f = proc (x) set x = 44 in let g = proc (y) (f y) in letmutable z = 55 in begin (g z); z end ") (num-val 44))
(check-equal? (run "let swap = proc (x) proc (y) let temp = x
                  in begin
                      set x = y;
                      set y = temp
                     end
      in letref a = 33
         in letmutable b = 44
            in begin
                ((swap a) b);
-(a,b) end") (num-val 11))
(check-equal? (run "letref b = 3
in let p = proc (x) proc(y)
                  begin
                   set x = 4;
                   y
                  end
         in ((p b) b)" ) (num-val 4))

(run "let
        swap = proc (x) proc (y) let temp = x
                  in begin
                      set x = y;
                      set y = temp
                     end
        ary = newarray(2,100)
        in begin arrayset(ary,0,1);
                 arrayset(ary,1,9);
                 print(arrayref(ary,0));
                 print(arrayref(ary,1));
                 ((swap arrayref(ary,0))  arrayref(ary,1));
                 print(arrayref(ary,0));
                 print(arrayref(ary,1))
                 
 end ")

;; test for lazy evaluation
(check-equal? (run " letrec infiniteloop (x) = (infiniteloop +(x,1)) in
           let f = proc (z) 11 in
            (f (infiniteloop 0))") (num-val 11))

;;exercise4.38
(check-equal? (run "
      let makerec = proc (f)
                     let d = proc (x) (f (x x))
in (f (d d)) in let maketimes4 = proc (f)
                           proc (x)
                            if zero?(x)
                            then 0
                            else +((f -(x,1)), 4)
in let times4 = (makerec maketimes4) in (times4 3)") (num-val 12))

;;exercise4.42
(check-equal? (run "let y = 100 in
                     lazylet x = begin print(-(y,1)); +(y,1) end
                       in begin print(y); +(x,1) end") (num-val 102))
                       