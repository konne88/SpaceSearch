
(define (number->unary n)
  (if (= n 0) '(O) `(S ,(number->unary (- n 1)))))

(define (unary->number n)
  (match n
    ((O) 0)
    ((S n) (add1 (unary->number n)))))

(define (format-solution n s)
  (match s
    ((Nil) '())
    ((Cons u s) (let ((x (unary->number u)))
      (cons (string-append (make-string  x #\.) "*" (make-string (- n x 1) #\.) "\n") (format-solution n s))))))

(define (format-result n r)
  (match r
    ((None) "No solution")
    ((Some s) (apply string-append (format-solution n s)))))

(define n (string->number (vector-ref (current-command-line-arguments) 0)))

(displayln (string-append "Solving n-queens problem for n = " (~a n)))

(displayln (~a (format-result n (solveNQueens (number->unary n)))))

