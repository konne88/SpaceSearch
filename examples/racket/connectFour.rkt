
(define (move->string m)
  (string-append
    "place on column "
    (number->string (unary->number m))))

(define (format-solution s)
  (define (format-response-list l indent)
    (foldl (lambda (p result)
      (match p
        ((Pair m s)
	 (string-append
	    result
	    indent
	    (move->string m)
	    ":\n"
	    indent
	    (helper s (string-append indent "  "))
	    "\n")))) "" l))

  (define (helper s indent)
    (string-append indent
      (match s
        ((FlatWin) "Win for red")
        ((FlatMoveToWin m)
          (string-append
	    "Red "
	    (move->string m)
	    " and wins"))
        ((FlatRespond m l)
          (string-append
            "Red "
	    (move->string m)
	    ". Black's moves, with Red's response:\n"
	    (format-response-list
	      (coqList->racketList l)
	      (string-append indent "  ")))))))
   (helper s ""))

(define (format-result r)
  (match r
    ((None) "Unknown solution")
    ((Some r) 
      (match r
    	((Uninhabited) "No solution")
    	((Solution a)
	  (string-append "Solution found:\n" (format-solution a)))))))

(define (char->piece char)
  (if (char=? char #\R) `(Some ,'(Red))
  (if (char=? char #\B) `(Some ,'(Black))
  `(None))))

(define (my-map proc l)
  (foldr (lambda (a acc) (cons (proc a) acc)) '() l))

(define (line->piece-list char-list)
  (my-map char->piece char-list))

(define (transpose-board board)
  (build-list 7 (lambda (y)
    (build-list 6 (lambda (x)
      (list-ref (list-ref board x) y))))))

(define (read-raw-board-file name)
  (define in (open-input-file name))
  (define lines (build-list 6 (lambda (n) (read-line in))))
  (my-map
    (lambda (ln)
      (define l (string->list ln))
      (if (eq? (length l) 7)
        l
	(error "Line too short, must be 7 wide")))
	lines))

(define (process-board raw-board)
  (racketList->coqList
    (my-map racketList->coqList
      (transpose-board (my-map line->piece-list raw-board)))))

(define (make-initial-state raw-board)
  `(Pair ,'(Red) ,(process-board raw-board)))

(define n (string->number (vector-ref (current-command-line-arguments) 0)))
(define file (vector-ref (current-command-line-arguments) 1))
(define board (read-raw-board-file file))

(displayln (string-append
  "Finding winning strategy for board in "
  file
  " to win in "
  (number->string n)
  " moves."))

(define init (make-initial-state board))

(displayln (format-result (@ solveConnectFourGame init (number->unary n))))
