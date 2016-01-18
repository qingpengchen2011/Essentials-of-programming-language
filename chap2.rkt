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


