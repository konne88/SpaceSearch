#lang s-exp rosette

(require
  racket/hash
  (only-in rosette term-cache constant? model sat)
  (only-in rosette/base/core/type solvable-default get-type))

(provide solve/evaluate/concretize)

(define concretize
  (case-lambda
    [(sol)
     (concretize sol (filter constant? (hash-values (term-cache))))]
    [(sol consts)
     (match sol
       [(model bindings)
        (sat
         (hash-union
          bindings
          (for/hash ([c consts] #:unless (dict-has-key? bindings c))
            (values c (solvable-default (get-type c))))))]
       [_ (error 'complete "expected a sat? solution, given ~a" sol)])]))

(define-syntax-rule (solve/evaluate/concretize expr)
  (let* ([out (void)]
         [sol (solve (set! out (expr (void))))])
    (if (unsat? sol) '(Empty)
      `(Solution ,(evaluate out (concretize sol))))))

