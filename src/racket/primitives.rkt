#lang s-exp rosette

(require "extraction.rkt")

(provide (all-defined-out))

(define (number->unary n)
  (if (= n 0) 
    '(O) 
    `(S ,(number->unary (- n 1)))))

(define (unary->number n)
  (match n
    ((O) 0)
    ((S n) (add1 (unary->number n)))))

(define (number->positive n)
  (if (= n 1) '(XH) (begin
    (define-values (q r) (quotient/remainder n 2))
    (if (= r 0)
      `(XO ,(number->positive q))
      `(XI ,(number->positive q))))))

(define (positive->number n)
  (match n
    ((XH) 1)
    ((XO n) (* 2 (positive->number n)))
    ((XI n) (+ 1 (* 2 (positive->number n))))))

(define (number->z n)
  (if (= n 0) '(Z0)
    (if (> n 0) 
      `(Zpos ,(number->positive n))
      `(Zneg ,(number->positive (- n))))))

(define (z->number n)
  (match n
    ((Z0) 0)
    ((Zpos n) (positive->number n))
    ((Zneg n) (* -1 (positive->number n)))))

(define (racketList->coqList l)
  (if (null? l) 
    '(Nil) 
    `(Cons ,(car l) ,(racketList->coqList (cdr l)))))

(define (coqList->racketList l)
  (match l 
    ((Nil) '()) 
    ((Cons h t) (cons h (coqList->racketList t)))))

