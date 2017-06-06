(define (coqNatPair->string p)
  (match p ((Pair x y)
    (string-append
      "("
      (number->string (unary->number x))
      ", "
      (number->string (unary->number y))
      ")"))))

(define (format-solution s)

  (define (format-response-list l indent)
    (foldl (lambda (p result)
      (match p
        ((Pair m s)
	 (string-append
	    result
	    indent
	    (coqNatPair->string m)
	    ":\n"
	    indent
	    (helper s (string-append indent "  "))
	    "\n")))) "" l))

  (define (helper s indent)
    (string-append indent
      (match s
        ((FlatWin) "Win for X")
        ((FlatMoveToWin m)
          (string-append
	    "X moves to "
	    (coqNatPair->string m)
	    " to win"))
        ((FlatRespond m l)
          (string-append
            "X moves to "
	    (coqNatPair->string m)
	    ". O's moves, with X's response:\n"
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

(define (line->shape-list line)
  (define char-list (string->list line))
  (define (char->shape char)
    (if (char=? char #\X)
      `(Some ,'(X))
      (if (char=? char #\O)
        `(Some ,'(O0))
	`(None))))
  (racketList->coqList
    (foldr (lambda (char acc) (cons (char->shape char) acc))
      '() char-list)))

(define (read-board-file name)
  (define in (open-input-file name))
  (define l0 (read-line in))
  (define l1 (read-line in))
  (define l2 (read-line in))
  (racketList->coqList
    (foldr (lambda (ln acc) (cons (line->shape-list ln) acc))
      '() (list l0 l1 l2))))

(define (make-initial-state board) `(Pair ,'(X) ,board))

(define n (string->number (vector-ref (current-command-line-arguments) 0)))
(define file (vector-ref (current-command-line-arguments) 1))
(define init (make-initial-state (read-board-file file)))

(displayln (string-append
  "Finding winning strategy for board in "
  file
  " to win in "
  (number->string n)
  " moves."))
(displayln (format-result (@ solveTicTacToeGame init (number->unary n))))
