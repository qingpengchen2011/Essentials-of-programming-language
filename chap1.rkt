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


;;occurs-free? Sym * LcExp -> Bool
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
             