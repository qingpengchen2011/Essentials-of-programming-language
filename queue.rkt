#lang racket
(define empty-queue
    (lambda ()
      '()))

  (define empty? null?)

  (define enqueue
    (lambda (q val)
      (append q (list val))))

  (define dequeue
    (lambda (q f)
      (f (car q) (cdr q))))

 (provide empty-queue enqueue dequeue empty?)
