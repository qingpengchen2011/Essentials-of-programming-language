#lang eopl

;;;section 1.1

;;in-S?: N -> Bool
(define in-S?
  (lambda (n)
    (if (zero? n)
        #t
        (if (>= (- n 3) 0)
            (in-S? (- n 3))
            #f))))

;;;section 1.2

;;list-length: List -> Int
(define list-length
  (lambda (lst)
    (if (null? lst)
        0
        (+ 1 (list-length (cdr lst))))))

;;nth-element: List * Int -> schemeVal
(define nth-element
  (lambda (lst n)
          (if (null? lst)
              (report-list-too-short n)
              (if (zero? n)
                  (car lst)
                  (nth-element (cdr lst) (- n 1))))))
(define report-list-too-short
  (lambda (n)
          (eopl:error 'nth-element
                      "List too short by ~s elements.~%" (+ n 1))))

;;remove-first: Sym * ListOfSym -> ListOfSym
(define remove-first
  (lambda (s los)
          (if (null? los)
              '()
              (if (eqv? s (car los))
                  (cdr los)
                  (cons (car los)
                        (remove-first s (cdr los)))))))

;;exercise1.9
;;remove: Sym * ListOfSym -> ListOfSym
(define remove
  (lambda (s los)
    (if (null? los)
        '()
        (if (eqv? s (car los))
            (remove s (cdr los))
            (cons (car los) (remove s (cdr los)))))))


;;occurs-free?:  Sym * LcExp -> Bool
(define occurs-free?
  (lambda (var exp)
    (cond
      ((symbol? exp) (eqv? var exp))
      ((eqv? 'lambda (car exp))
       (and (not (eqv? var (car (cadr exp))))
            (occurs-free? var (caddr exp))))
      (else
       (or (occurs-free? var (car exp))
           (occurs-free? var (cadr exp)))))))

;;subst: Sym * Sym * S-list -> S-list
(define subst
  (lambda (old new slist)
    (if (null? slist)
        '()
        (cons (subst-in-s-exp old new (car slist))
              (subst old new (cdr slist))))))
;;subst-in-s-exp: Sym * Sym * S-exp -> S-exp
(define subst-in-s-exp
  (lambda (old new sexp)
    (if (symbol? sexp)
        (if (eqv? old sexp)
            new
            sexp)
        (subst old new sexp))))
;;exercise1.12
;;subst2: Sym * Sym * S-list -> S-list
(define subst2
  (lambda (old new slist)
    (if (null? slist)
        '()
        (cons (if (symbol? (car slist))
                  (if (eqv? old (car slist))
                      new
                      (car slist))
                  (subst2 old new (car slist)))
              (subst2 old new (cdr slist))))))

;;exercise1.13
;;subst3: Sym * Sym * S-list -> S-list
(define subst3
  (lambda (old new slist)
    (map (lambda (sexp)
           (if (symbol? sexp)
               (if (eqv? old sexp)
                   new
                   sexp)
               (subst3 old new sexp)))
         slist)))

;;section 1.3
;;number-elements-from: ListOf(SchemeVal) * Int -> ListOf(List(Int,SchemeVal))
(define number-elements-from
  (lambda (lst n)
    (if (null? lst)
        '()
        (cons (list n (car lst))
              (number-elements-from (cdr lst) (+ n 1))))))
(define number-elements
  (lambda (lst)
    (number-elements-from lst 0)))

;;;section1.4 exercises

;;exercise1.15
;;duple: Int * SchemeVal -> ListOf(SchemeVal)
(define duple
  (lambda (n x)
    (if (zero? n)
        '()
        (cons x (duple (- n 1) x)))))

;;exercise1.16
;;invert:
(define invert
  (lambda (lst)
    (if (null? lst)
        '()
        (cons (swap (car lst))
              (invert (cdr lst))))))
(define swap
  (lambda (lst)
          (list (cadr lst)
                (car lst))))

;;exercise1.17
(define down
  (lambda (lst)
    (if (null? lst)
        '()
        (cons (list (car lst))
              (down (cdr lst))))))

;;exercise1.18
(define swrapper
  (lambda (s1 s2 slist)
    (if (null? slist)
        '()
        (cons (swrapper-s-exp s1 s2 (car slist))
              (swrapper s1 s2 (cdr slist))))))
(define swrapper-s-exp
  (lambda (s1 s2 sexp)
    (if (symbol? sexp)
        (cond ((eqv? s1 sexp) s2)
              ((eqv? s2 sexp) s1)
              (else sexp))
        (swrapper s1 s2 sexp))))
