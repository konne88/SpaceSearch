(define (number->unary n)
  (if (= n 0) '(O) `(S ,(number->unary (- n 1)))))

(define (unary->number n)
  (match n
    ((O) 0)
    ((S n) (add1 (unary->number n)))))

(define (format-result n r)
  (match r
    ((Uninhabited) "No solution")
    ((Solution s) (number->string (unary->number s)))))

(define n (string->number (vector-ref (current-command-line-arguments) 0)))

(displayln
   (string-append "Searching for primes for n even numbers after 2, n = "
      (~a n)))

(displayln (~a (format-result n (primeSearch (number->unary n)))))
