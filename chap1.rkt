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

;;exercise1.19
(define list-set
  (lambda (lst n x)
    (if (null? lst)
        (eopl:error 'list-set
                    "list too short")
        (if (zero? n)
            (cons x (cdr lst))
            (cons (car lst) (list-set (cdr lst) (- n 1) x))))))

;;exercise1.20
(define count-occurrences
  (lambda (s slist)
    (if (null? slist)
        0
        (+ (count-occurrences-in-sexp s (car slist))
           (count-occurrences s (cdr slist))))))
(define count-occurrences-in-sexp
  (lambda (s sexp)
    (if (symbol? sexp)
        (if (eqv? s sexp)
            1
            0)
        (count-occurrences s sexp))))

;;exercise1.21
(define product
  (lambda (sos1 sos2)
    (if (null? sos1)
        '()
        (append (map (lambda (sym2)
                       (list (car sos1) sym2))
                     sos2)
                (product (cdr sos1) sos2)))))

;;exercise1.22
(define filter-in
  (lambda (pred lst)
    (if (null? lst)
        '()
        (if (pred (car lst))
            (cons (car lst) (filter-in pred (cdr lst)))
            (filter-in pred (cdr lst))))))

;;exercise1.23
(define list-index
  (lambda (pred lst)
    (list-index-n pred lst 0)))
(define list-index-n
  (lambda (pred lst i)
    (if (null? lst)
        #f
        (if (pred (car lst))
            i
            (list-index-n pred (cdr lst) (+ i 1))))))

;;exercise1.24
(define every?
  (lambda (pred lst)
    (if (null? lst)
        #t
        (if (pred (car lst))
            (every? pred (cdr lst))
            #f))))

;;exercise1.25
(define exist?
  (lambda (pred lst)
    (if (null? lst)
        #f
        (if (pred (car lst))
            #t
            (exist? pred (cdr lst))))))

;;exercise1.26
(define up
  (lambda (lst)
    (if (null? lst)
        '()
        (if (list? (car lst))
            (append (car lst) (up (cdr lst)))
            (cons (car lst) (up (cdr lst)))))))

;;exercise1.27
(define flatten
  (lambda (slist)
    (if (null? slist)
        '()
        (append (flatten-s-exp (car slist))
                (flatten (cdr slist))))))
(define flatten-s-exp
  (lambda (sexp)
    (if (symbol? sexp)
        (list sexp)
        (flatten sexp))))

;;exercise1.28
(define merge
  (lambda (loi1 loi2)
    (cond ((null? loi1) loi2)
          ((null? loi2) loi1)
          ((<= (car loi1) (car loi2)) (cons (car loi1)
                                            (merge (cdr loi1) loi2)))
          (else
           (cons (car loi2)
                 (merge loi1 (cdr loi2)))))))

;;exercise1.29
(define sort
  (lambda (lst)
    (if (null? lst)
        '()
        (insert-at (car lst) (sort (cdr lst))))))
(define insert-at
  (lambda (n lst)
    (if (null? lst)
        (list n)
        (if (>= n (car lst))
            (cons (car lst) (insert-at n (cdr lst)))
            (cons n lst)))))
;;exercise1.30
(define sort/predicate
  (lambda (pred loi)
    (if (null? loi)
        '()
        (insert-at-withpred pred (car loi) (sort/predicate pred (cdr loi))))))
(define insert-at-withpred
  (lambda (pred i loi)
          (if (null? loi)
              (list i)
              (if (pred i (car loi))
                  (cons i loi)
                  (cons (car loi) (insert-at-withpred pred i (cdr loi)))))))

;;exercise1.31
(define leaf
  (lambda (n)
          n))

(define interior-node
  (lambda (sym ltree rtree)
    (list sym ltree rtree)))

(define leaf?
  (lambda (bintree)
          (not (list? bintree))))

(define lson
  (lambda (bintree)
    (cadr bintree)))

(define rson
  (lambda (bintree)
    (caddr bintree)))

(define contents-of
  (lambda (bintree)
    (if (leaf? bintree)
        bintree
        (car bintree))))

;;exercise1.32
(define double-tree
  (lambda (bintree)
    (if (leaf? bintree)
        (* 2 bintree)
        (interior-node (contents-of bintree)
                       (double-tree (lson bintree))
                       (double-tree (rson bintree))))))


;;exercise1.33
(define mark-leaves-with-red-depth
  (lambda (bintree)
    (mark-leaves-with-red-depth-beginwith 0 bintree)))
(define mark-leaves-with-red-depth-beginwith
  (lambda (n bintree)
    (if (leaf? bintree)
        n
        (if (eqv? 'red (contents-of bintree))
            (interior-node (contents-of bintree)
                           (mark-leaves-with-red-depth-beginwith (+ n 1) (lson bintree))
                           (mark-leaves-with-red-depth-beginwith (+ n 1) (rson bintree)))
            (interior-node (contents-of bintree)
                           (mark-leaves-with-red-depth-beginwith n (lson bintree))
                           (mark-leaves-with-red-depth-beginwith n (rson bintree)))))))

;;exercise1.34
(define path
  (lambda (n bintree)
    (if (= n (contents-of bintree))
        '()
        (if (< (contents-of bintree) n)
            (cons 'right (path n (rson bintree)))
            (cons 'left (path n (lson bintree)))))))

;;exercise1.35
(define number-leaves
  (lambda (bintree)
    (cadr (count-and-change-leaves bintree 0))))
(define count-and-change-leaves
  (lambda (bintree n)
    (if (leaf? bintree)
        (list (+ n 1) n)
        (let ((newleft (count-and-change-leaves (lson bintree) n)))
          (let ((newright (count-and-change-leaves (rson bintree) (car newleft))))
            (list (car newright)
                  (interior-node (contents-of bintree)
                                 (cadr newleft)
                                 (cadr newright))))))))
               

;;exercise1.36
(define number-elements-g
  (lambda (lst)
    (if (null? lst)
        '()
        (g (list 0 (car lst))
           (number-elements-g (cdr lst))))))
(define g
  (lambda (h t)
    (cons h
    (map (lambda (p)
           (cons (+ (car p) 1)
                 (cdr p))) t))))
               