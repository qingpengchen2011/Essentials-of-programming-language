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
  (bool-exp (exp1 boolexpression?))
  (if-bool-exp (exp1 boolexpression?) (exp2 expression?) (exp3 expression?))
  (var-exp (var identifier?))
  (let-exp (var identifier?) (exp1 expression?) (body expression?))
  (emptylist-exp)
  (cons-exp (exp1 expression?) (exp2 expression?))
  (car-exp (exp expression?))
  (cdr-exp (exp expression?))
  (list-exp (exps (list-of expression?)))
  (cond-exp (preds (list-of boolexpression?)) (consequences (list-of expression?)))
  (print-exp (exp expression?))
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
  (list-val (list (list-of expval?))))


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
              
      (let-exp (var exp1 body)
               (value-of body (extend-env var (value-of exp1 env) env)))
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
                 (begin (eopl:printf "~s" (value-of exp env)) (num-val 1))))))

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
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("cond" "{" (arbno boolexpression "==>" expression) "}" "end") cond-exp)
    (expression ("print" "(" expression ")") print-exp)

    (boolexpression ("equal?" "(" expression "," expression ")") equal?-bool-exp)
    (boolexpression ("zero?" "(" expression ")") zero?-bool-exp)
    (boolexpression ("greater?" "(" expression "," expression ")") greater?-bool-exp)
    (boolexpression ("less?" "(" expression "," expression ")") less?-bool-exp)
    (boolexpression ("null?" "(" expression ")") null?-bool-exp)
    
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
                                    } end 
)")
