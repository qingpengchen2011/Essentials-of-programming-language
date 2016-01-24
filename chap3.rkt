#lang eopl

(require  "./chap2.rkt")
(require  "./chap2-from-section2.4-to-end.rkt")



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
  (zero?-exp (exp1 expression?))
  (equal?-exp (exp1 expression?) (exp2 expression?))
  (greater?-exp (exp1 expression?) (exp2 expression?))
  (less?-exp (exp1 expression?) (exp2 expression?))
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
    (define arithmetic-operation
      (lambda (op exp1 exp2 env)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (num-val (op (expval->num val1) (expval->num val2))))))
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
      
      (zero?-exp (exp)
                 (let ((val (value-of exp env)))
                   (if (zero? (expval->num val))
                       (bool-val #t)
                       (bool-val #f))))
      (equal?-exp (exp1 exp2)
                  (let ((val1 (value-of exp1 env))
                        (val2 (value-of exp2 env)))
                    (if (eqv? (expval->num val1) (expval->num val2))
                        (bool-val #t)
                        (bool-val #f))))
      (greater?-exp (exp1 exp2)
                   (let ((val1 (value-of exp1 env))
                         (val2 (value-of exp2 env)))
                     (bool-val (> (expval->num val1) (expval->num  val2)))))
      (less?-exp (exp1 exp2)
                 (let ((val1 (value-of exp1 env))
                       (val2 (value-of exp2 env)))
                   (bool-val (< (expval->num val1) (expval->num val2)))))
                    

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
    (expression ("minus" "(" expression ")") minus-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" expression "," expression ")") add-exp)
    (expression ("*" "(" expression "," expression ")") multiply-exp)
    (expression ("//" "(" expression "," expression ")") quotient-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("equal?" "(" expression "," expression ")") equal?-exp)
    (expression ("greater?" "(" expression "," expression ")") greater?-exp)
    (expression ("less?" "(" expression "," expression ")") less?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    ))

(define scan&parse
    (sllgen:make-string-parser lexical-spec grammer-spec))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

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

