
(define (number->unary n)
  (if (= n 0) '(O) `(S ,(number->unary (- n 1)))))

(define ((format-solution s) x y)
  (match s
    ((Nil) " .")
    ((Cons xy s) 
      (if (eq? xy `(Pair ,x ,y)) " *"
        ((format-solution s) x y)))))

(define (sample w h f)
  (string-join (for/list ([y h]) 
    (string-join (for/list ([x w])
      (f x y)) "")) "\n"))

(define (format-result n r)
  (match r
    ((Uninhabited) "No solution")
    ((Solution s) (sample n n (format-solution s)))))

(define n (string->number (vector-ref (current-command-line-arguments) 0)))

(displayln (string-append "Solving n-queens problem for n = " (~a n)))

(displayln (format-result n (solveNQueens (number->unary n))))

