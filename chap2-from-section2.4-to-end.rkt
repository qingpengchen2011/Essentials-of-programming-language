#lang eopl
;;section 2.4



(define-datatype lc-exp lc-exp?
  (var-exp (var identifier?))
  (lambda-exp (bound-var identifier?)
              (body lc-exp?))
  (app-exp (rator lc-exp?)
           (rand lc-exp?)))

;;exercise2.21
(define-datatype environment environment?
  (empty-env)
  (extend-env (var identifier?)
              (val (lambda (v) #t))
              (saved-env environment?)))
(define has-binding?
  (lambda (search-var env)
    (cases environment env
      (empty-env () #f)
      (extend-env (var val saved-env)
                  (if (eqv? var search-var)
                      #t
                  (has-binding? search-var saved-env))))))

;;exercise2.23
(define identifier?
  (lambda (id)
    (and (symbol? id)
         (not (eqv? 'lambda id)))))