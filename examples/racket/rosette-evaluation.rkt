#!/usr/bin/env racket
#lang s-exp rosette

(current-bitwidth #f)

(define-syntax-rule (solve/evaluate expr)
  (let* ([out (void)]
         [sol (solve (set! out expr))])
    (if (unsat? sol) 'uninhabited
    (if (unknown? sol) 'unknown
      (evaluate out sol)))))

(define (symbolic-bool)
  (define-symbolic* b boolean?) b)

(printf "Solve value: ~a\n" (solve/evaluate 5))

(printf "Bound symbolic: ~a\n" (solve/evaluate
  (let ([x (symbolic-bool)])
    (and x (not x)))))

(printf "Inlinded symbolic: ~a\n" (solve/evaluate 
  (and (symbolic-bool) (not (symbolic-bool)))))

(printf "Bound assert: ~a\n" (solve/evaluate
  (let ([x (assert false)])
    (if (symbolic-bool) 42 x))))

(printf "Inlinded assert: ~a\n" (solve/evaluate 
  (if (symbolic-bool) 42 (assert #f))))

(printf "De Morgan's law: ~a\n" (solve/evaluate
  (let ([x (symbolic-bool)] [y (symbolic-bool)])
    (if (eq? (and x y) (not (or (not x) (not y))))
	(assert false) (cons x y)))))

(printf "Nested search: ~a\n"
  (solve/evaluate 
    (if (symbolic-bool) (assert false) 
      (solve/evaluate (if (symbolic-bool) (assert false) 42)))))

(printf "Nested search': ~a\n"
  (solve/evaluate (let ([b (symbolic-bool)])
    (solve/evaluate (if b 4 (assert false))))))

