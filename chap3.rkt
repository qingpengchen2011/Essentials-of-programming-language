#lang eopl

(require  "./chap2.rkt")
(require  "./chap2-from-section2.4-to-end.rkt")



;;section3.2 LET: A Simple Language

(define-datatype program program?
  (a-program (exp expression?)))

(define-datatype expression expression?
  (const-exp (num number?))
  (diff-exp (exp1 expression?) (exp2 expression?))
  (zero?-exp (exp1 expression?))
  (if-exp (exp1 expression?) (exp2 expression?) (exp3 expression?))
  (var-exp (var identifier?))
  (let-exp (var identifier?) (exp1 expression?) (body expression?)))

;;define expressed value
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?)))


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

(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (num-val (- (expval->num val1) (expval->num val2)))))
      (zero?-exp (exp)
                 (let ((val (value-of exp env)))
                   (if (zero? (expval->num val))
                       (bool-val #t)
                       (bool-val #f))))

     (if-exp (exp1 exp2 exp3)
             (if (expval->bool (value-of exp1 env))
                 (value-of exp2 env)
                 (value-of exp3 env)))
      (let-exp (var exp1 body)
               (value-of body (extend-env var (value-of exp1 env) env))))))


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
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    ))

(define scan&parse
    (sllgen:make-string-parser lexical-spec grammer-spec))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))


