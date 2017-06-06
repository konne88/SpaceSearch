(define (coqZPair->string p)
  (match p ((Pair x y)
    (string-append
      "("
      (number->string (z->number x))
      ", "
      (number->string (z->number y))
      ")"))))

(define (piece->string p)
  (match p
    ((King) "king")
    ((Queen) "queen")
    ((Knight) "knight")
    ((Bishop) "bishop")
    ((Rook) "rook")
    ((Pawn) "pawn")))

(define (move->string m)
  (match m
    ((Pair p1 c2)
      (match p1
         ((Pair piece c1)
	  (string-append
  	    (piece->string piece)
            " from "
	    (coqZPair->string c1)
	    " to "
	    (coqZPair->string c2)))))))

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
        ((FlatWin) "Win for white")
        ((FlatMoveToWin m)
          (string-append
	    "White moves "
	    (move->string m)
	    " to win"))
        ((FlatRespond m l)
          (string-append
            "White moves "
	    (move->string m)
	    ". Black's moves, with White's response:\n"
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
  (if (char=? char #\p) `(Some ,`(Pair ,'(Black) ,'(Pawn)))
  (if (char=? char #\n) `(Some ,`(Pair ,'(Black) ,'(Knight)))
  (if (char=? char #\b) `(Some ,`(Pair ,'(Black) ,'(Bishop)))
  (if (char=? char #\r) `(Some ,`(Pair ,'(Black) ,'(Rook)))
  (if (char=? char #\q) `(Some ,`(Pair ,'(Black) ,'(Queen)))
  (if (char=? char #\k) `(Some ,`(Pair ,'(Black) ,'(King)))
  (if (char=? char #\P) `(Some ,`(Pair ,'(White) ,'(Pawn)))
  (if (char=? char #\N) `(Some ,`(Pair ,'(White) ,'(Knight)))
  (if (char=? char #\B) `(Some ,`(Pair ,'(White) ,'(Bishop)))
  (if (char=? char #\R) `(Some ,`(Pair ,'(White) ,'(Rook)))
  (if (char=? char #\Q) `(Some ,`(Pair ,'(White) ,'(Queen)))
  (if (char=? char #\K) `(Some ,`(Pair ,'(White) ,'(King)))
  `(None))))))))))))))

(define (my-map proc l)
  (foldr (lambda (a acc) (cons (proc a) acc)) '() l))

(define (line->piece-list char-list)
  (my-map char->piece char-list))

(define (read-raw-board-file name)
  (define in (open-input-file name))
  (define lines (build-list 8 (lambda (n) (read-line in))))
  (my-map
    (lambda (ln)
      (define l (string->list ln))
      (if (eq? (length l) 8)
        l
	(error "Line too short, must be 8 wide")))
	lines))
  
(define (process-board raw-board)
  (racketList->coqList
    (my-map
      (lambda (ln) (racketList->coqList (line->piece-list ln)))
        raw-board)))

(define (find-piece-coords raw-board piece)
  (define (find-in-row row acc x y)
    (if (empty? row)
      acc
      (begin
        (define hd (car row))
	(if (char=? hd piece)
	  (find-in-row (cdr row) (list* (list x y) acc) x (+ y 1))
	  (find-in-row (cdr row) acc x (+ y 1))))))
  (define (helper raw-board acc x)
    (if (empty? raw-board)
      acc
      (begin
        (define row (car raw-board))
	(define finds (find-in-row row acc x 0))
	(helper (cdr raw-board) finds (- x 1)))))
  (helper raw-board '() 7))

(define (coord->z-pair coord)
  (define x (number->z (car coord)))
  (define y (number->z (cadr coord)))
  `(Pair ,x ,y))

(define (find-white-king raw-board)
  (define all-kings (find-piece-coords raw-board #\K))
  (if (eq? (length all-kings) 1)
    (coord->z-pair (car all-kings))
    (error "There must be exactly one white king on the board")))

(define (find-black-king raw-board)
  (define all-kings (find-piece-coords raw-board #\k))
  (if (eq? (length all-kings) 1)
    (coord->z-pair (car all-kings))
    (error "There must be exactly one black king on the board")))

(define (make-initial-state raw-board)
  `(Pair
    ,`(Pair
      ,`(Pair ,(process-board raw-board) ,`(White))
      ,(find-black-king raw-board))
    ,(find-white-king raw-board)))

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

(displayln (format-result (@ solveChessGame init (number->unary n))))
