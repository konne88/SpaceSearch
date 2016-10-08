(define n (string->number (vector-ref (current-command-line-arguments) 0)))

(system "service ssh start")

(printf "squaring the sequence 0..~a:\n" n)

(displayln
  (sort
    (for/list ([n (coqList->racketList 
                    (squareList 
                      (number->unary (+ 1 n))))])
      (unary->number n)) <))

