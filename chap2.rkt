#lang eopl




;;;section2.2.2
(define empty-env
  (lambda ()
    (list 'empty-env)))

(define extend-env
  (lambda (var val env)
    (list 'extend-env var val env)))

(define apply-env
  (lambda (env search-var)
    (cond ((eqv? 'empty-env (car env))
           (report-no-binding-found search-var))
          ((eqv? 'extend-env (car env))
           (let ((saved-var (cadr env))
                 (saved-val (caddr env))
                 (saved-env (cadddr env)))
             (if (eqv? search-var saved-var)
                 saved-val
                 (apply-env saved-env search-var))))
          (else
           report-invalid-env env))))


(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environments ~s" env)))


;;;section2.2.3
(define empty-env-p
  (lambda ()
    (lambda (search-var)
      (report-no-binding-found search-var))))

(define extend-env-p
  (lambda (var val env)
    (lambda (search-var)
      (if (eqv? search-var var)
          val
          (apply-env-p env search-var)))))
(define apply-env-p
  (lambda (env search-var)
    (env search-var)))

;;section2.3
;;exercise2.15
(define var-exp
  (lambda (var)
    var))

(define lambda-exp
  (lambda (var lc-exp)
    (list 'lambda var lc-exp)))

(define app-exp
  (lambda (rator rand)
    (list 'application rator rand)))

(define var-exp?
  (lambda (exp)
    (not (list? exp))))

(define lambda-exp?
  (lambda (exp)
    (and (list? exp)
         (eqv? 'lambda (car exp)))))

(define app-exp?
  (lambda (exp)
    (and (list? exp)
         (eqv? 'application (car exp)))))

(define var-exp->var
  (lambda (exp)
          exp))

(define lambda-exp->bound-var
  (lambda (exp)
    (cadr exp)))

(define lambda-exp->body
  (lambda (exp)
    (caddr exp)))

(define app-exp->rator
  (lambda (exp)
    (cadr exp)))

(define app-exp->rand
  (lambda (exp)
    (caddr exp)))

(define occurs-free?
  (lambda (search-var LcExp)
    (cond ((var-exp? LcExp)
           (eqv? search-var (var-exp->var LcExp)))
          ((lambda-exp? LcExp)
           (and (not (eqv? search-var (lambda-exp->bound-var LcExp)))
                (occurs-free? search-var (lambda-exp->body LcExp))))
          ((app-exp? LcExp)
           (or (occurs-free? search-var (app-exp->rator LcExp))
               (occurs-free? search-var (app-exp->rand LcExp))))
          (else
           (eopl:error 'occurs-free? "invalid LcExp ~s" LcExp)))))
           

;;exercise2.18
(define number->sequence
  (lambda (number)
    (list number '() '())))


(define current-element
  (lambda (seq)
    (car seq)))

(define move-to-left
  (lambda (seq)
    (let ((current (current-element seq))
          (left-hand (cadr seq))
          (right-hand (caddr seq)))
      (if (null? left-hand)
          (eopl:error 'move-to-left "~s is at left end" seq)
          (list (car left-hand)
                (cdr left-hand)
                (cons current right-hand))))))

(define move-to-right
  (lambda (seq)
    (let ((current (current-element seq))
          (left-hand (cadr seq))
          (right-hand (caddr seq)))
      (if (null? right-hand)
          (eopl:error 'move-to-right "~s is at right end" seq)
          (list (car right-hand)
                (cons current left-hand)
                (cdr right-hand))))))

;;exercise2.19

(define number->bintree
  (lambda (number)
    (list number '() '())))

(define current-tree-element
  (lambda (bintree)
    (car bintree)))

(define move-to-left-son
  (lambda (bintree)
    (cadr bintree)))

(define move-to-right-son
  (lambda (bintree)
    (caddr bintree)))

(define at-leaf?
  (lambda (bintree)
    (null? bintree)))
               

(define insert-to-left
  (lambda (number bintree)
    (letrec ((current-element (current-tree-element bintree))
          (left-son (move-to-left-son bintree))
          (right-son (move-to-right-son bintree))
          (new-left-son (list number left-son '())))
      (list current-element new-left-son right-son))))

(define insert-to-right
  (lambda (number bintree)
    (letrec ((current-element (current-tree-element bintree))
          (left-son (move-to-left-son bintree))
          (right-son (move-to-right-son bintree))
          (new-right-son (list number '() right-son)))
      (list current-element left-son new-right-son))))
          



             

