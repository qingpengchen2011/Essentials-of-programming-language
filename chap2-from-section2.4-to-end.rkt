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

;;exercise2.24
(define-datatype bintree bintree?
  (leaf-node (num integer?))
  (interior-node
   (key symbol?)
   (left bintree?)
   (right bintree?)))

(define bintree-to-list
  (lambda (bt)
    (cases bintree bt
      (leaf-node (num)
                 (list 'leaf-node num))
      (interior-node (key left right)
                     (list 'interior-node key (bintree-to-list left) (bintree-to-list right))))))

;;exercise2.25
(define tree-1
  (interior-node 'foo (leaf-node 2) (leaf-node 3)))
(define tree-2
  (interior-node 'bar (leaf-node -1) tree-1))
(define tree-3
  (interior-node 'baz tree-2 (leaf-node 1)))

(define max-interior
  (lambda (btree)
    (define search-max-interior
      (lambda (bt)
        (cases bintree bt
          (leaf-node (num) (list num 'leaf-node num 'leaf-node)) ;;(current-sum current-node max-sum max-node)
          (interior-node (key left right)
                         (letrec ((left-data (search-max-interior left))
                               (right-data (search-max-interior right))
                               (left-current-sum (car left-data))
                               (left-current-sum-node (cadr left-data))
                               (left-max-sum (caddr left-data))
                               (left-max-node (cadddr left-data))
                               (right-current-sum (car right-data))
                               (right-current-sum-node (cadr right-data))
                               (right-max-sum (caddr right-data))
                               (right-max-node (cadddr right-data)))
                           (letrec ((current-sum (+ left-current-sum right-current-sum))
                                    (child-max (if (>= left-max-sum right-max-sum)
                                                   (list left-max-sum left-max-node)
                                                   (list right-max-sum right-max-node)))
                                    (current-max (if (>= current-sum (car child-max))
                                                     (list current-sum key)
                                                     child-max)))
                             (cons current-sum
                                   (cons key
                                         current-max))))))))
     (cadddr (search-max-interior btree))))

;;section2.5
(define parse-expression
  (lambda (datum)
    (cond ((symbol? datum) (var-exp datum))
          ((pair? datum)
           (if (eqv? 'lambda (car datum))
               (lambda-exp (car (cadr datum))
                           (parse-expression (caddr datum)))
               (app-exp (parse-expression (car datum))
                        (parse-expression (cadr datum)))))
          (else (eopl:error 'parse-expression "indvalid expression:~s" datum)))))

(define unparse-lc-expression
  (lambda (exp)
    (cases lc-exp exp
      (var-exp (var) var)
      (lambda-exp (bound-var body)
                  (list 'lambda (list bound-var) (unparse-lc-expression body)))
      (app-exp (rator rand)
               (list (unparse-lc-expression rator) (unparse-lc-expression rand))))))