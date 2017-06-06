Require Import Bool.
Require Import Basic.
Require Import Heuristic.
Require Import Full.
Require Import ListEx.
Require Import Integer.
Require Import EnsemblesEx.
Require Import EqDec.
Require Import Space.Tactics.
Require Import Program.
Require Import Classical.
Require Import List.

Module Type GameRules.
  Parameter state : Set.
  Parameter move : Set.

  Parameter execute_move : state -> move -> state.
  Parameter enumerate_legal_moves : state -> list move.
  Parameter win_state : state -> Prop.

  Axiom win_state_dec : forall (s : state), {win_state s} + {~win_state s}.

  Axiom movEq : eqDec move.
End GameRules.
  
Module GamePlayer (Import R : GameRules).    
  Definition legal_move (s : state) (m : move) : Prop :=
    In m (enumerate_legal_moves s).

  Definition legal_move_dec : forall (s : state) (m : move),
      {legal_move s m} + {~legal_move s m}.
  Proof. 
    intros. unfold legal_move.
    eapply (in_dec _ m (enumerate_legal_moves s)).
    Unshelve.
    apply movEq.
  Defined.    
    
  Inductive strategy (s : state) :=
  | win : win_state s -> strategy s
  | moveToWin (m : move) :
      legal_move s m -> win_state (execute_move s m) -> strategy s
  | moveToRespond (m : move) :
      legal_move s m -> ~win_state (execute_move s m)
      -> response (execute_move s m)
      -> strategy s
  with response (s : state) :=
    (* intuition here is r is each possible opposing move and there 
     * is a strategy to counter it *)
    counters : list {r : move & strategy (execute_move s r)} -> response s.

  Definition has_response (s : state) (r : response s) (m : move) : Prop.
    inversion r as [l].
    refine (In m (map _ l)).
    eapply projT1.
  Defined.

  Definition has_response_dec : forall (s : state) (r : response s) (m : move),
      {has_response s r m} + {~has_response s r m}.
  Proof.
    intros.
    destruct r.
    unfold has_response.
    eapply (in_dec _ m (map _ l)).
    Unshelve.
    eapply movEq.
  Defined.
        
  (* due to restrictions regarding strictly positive occurrences, I could
   * not characterize the type of response to give to enemy moves above,
   * so we define this additional stipulation (that each response must
   * correspond to an enemy moves) which we will prove applies *)
  Definition valid_response (s : state) (r : response s) :=
    let legal_moves := enumerate_legal_moves s in
    legal_moves <> [] /\
    forall (m : move), In m legal_moves -> has_response s r m.

  Definition valid_response_dec : forall (s : state) (r : response s),
      {valid_response s r} + {~valid_response s r}.
  Proof.
    intros.
    destruct r.
    unfold valid_response.
    induction (enumerate_legal_moves s).
    * right. intro H. destruct H; intuition.
    * destruct (has_response_dec s (counters s l) a) as [ Hresp | Hresp ].
      + destruct IHl0 as [IH | IH].
        - left. split; try congruence.
          intros m H. inversion H; try intuition.
          subst. assumption.
        - destruct l0.
          ** left. split; try congruence.
             intros m H. inv H; try assumption. inversion H0.
          ** right. intro H. destruct H as [H1 H2].
             apply IH. split; try congruence.
             intros m0 H'. apply H2.
             intuition.
       + right. intro H. destruct H as [H1 H2].
         apply Hresp. apply H2. intuition.
   Defined.

  Definition counter (s : state) (r : response s) (m : move)
    : option (strategy (execute_move s m)).
    destruct r.
    induction l as [| h t].
    * exact None. (* empty list, no counter *)
    * destruct h as [r strat].
      assert ({m = r} + {m <> r}) as H' by apply movEq.
      destruct H'.
      + subst. exact (Some strat).
      + apply IHt.
  Defined.

  Fixpoint spaceOfList `{Basic} {A} (l : list A) : Space A :=
    match l with
    | [] => empty
    | h :: t => union (single h) (spaceOfList t)
    end.

  Fixpoint listOfSpacesToSpaceOfLists `{Basic} {A}
           (ls : list (Space A)) : Space (list A) :=
    match ls with
    | [] => empty
    | h :: [] => bind h (fun a => single [a])
    | h :: t =>
      bind h (fun a =>
                bind (listOfSpacesToSpaceOfLists t)
                     (fun t' => single (a :: t')))
    end.

  (* given state s and a function from states to a space of strategies
   * (i.e., a bind over states to strategies), return a space of
   * all possible (valid) responses to opponent moves *)
  Definition spaceOfResponses `{Basic} (s : state)
             (stratSpace : forall (s' : state), Space (strategy s'))
    : Space (response s).
    (* all possible opposing moves *)
    refine (let responses := enumerate_legal_moves s in _).
    (* we want to map responses to a list of 
     * Space {m: move & strategy (execute_move s m)}, then
     * bind over those to obtain a space of responses *)
    refine (let strat_spaces :=
                listOfSpacesToSpaceOfLists (map _ responses) in _).
    refine (bind strat_spaces _).
    refine (fun l => single _).
    econstructor. exact l.
    Unshelve.
    (* converting a move to 
     * a Space {m : move & strategy (execute_move s m)} *)
    intro m.
    refine (let s' := execute_move s m in _).
    refine (let strat_space := stratSpace s' in _).
    refine (bind strat_space _).
    intro strat.
    refine (single _).
    econstructor. exact strat.
  Defined.
        
  Fixpoint strategySpace `{Basic} (bound : nat) : forall (s : state), Space (strategy s).
    intro s.
    destruct (win_state_dec s) as [w | w].
    (* we're in a winning state -> done no matter the bound *)
    exact (single (win s w)).
    (* no winning state, now we must recurse *)
    (* note that if the bound is 0 and we didn't win, there's nothing
     * we can do *)
    refine (match bound with O => empty | S n => _ end).
    (* bound is S n -> either win in one move or prepare a response *)
    * refine (bind (spaceOfList (enumerate_legal_moves s)) _).
      intro m.      
      destruct (legal_move_dec s m) as [l | l].
      (* because we're selecting form the list of legal moves,
       * any m we come up with will be legal *)
      + refine (let s' := execute_move s m in _).
        destruct (win_state_dec s') as [w' | w'].
        (* m is a winning move, so we're done *)
        - refine (single (moveToWin s m l w')).
        (* m is not a winning move, so we consider all possible responses
         * within the bound *)
        - refine (bind (spaceOfResponses s' (strategySpace _ n))
                       (fun r => _)).
          destruct (valid_response_dec s' r).
          (* Only return valid responses. Would have loved to bake
           * this into the constructor for strategies, but couldn't *)
          ** exact (single (moveToRespond s m l w' r)).
          ** exact empty.
      (* illegal move -- should never happen, by definition *)
      + exact empty.
  Defined.

  (* For easier printing *)
  Inductive flatStrategy :=
  | flatWin : flatStrategy
  | flatMoveToWin : move -> flatStrategy
  | flatRespond : move -> list (move * flatStrategy) -> flatStrategy
  .

  Fixpoint flattenStrat (s : state) (strat : strategy s) : flatStrategy.
    destruct strat.
    (* winning move *)
    * exact flatWin.
    (* one move to win *)
    * exact (flatMoveToWin m).
    (* move and response *)
    * refine (flatRespond m _).
      destruct r as [l'].
      refine (map (fun pair => _) l').
      destruct pair as [m' strat'].
      refine (let s' := execute_move (execute_move s m) m' in _).
      exact ((m', flattenStrat s' strat')).
  Defined.

  (* alternate version of strategy search without dependent types 
   * would be interesting to prove equivalence... *)
  Fixpoint flatStrategySpace `{Basic} (bound : nat) (s : state) : Space flatStrategy :=
    if win_state_dec s then single flatWin
    else
      match bound with
      | O => empty
      | S n =>
        let moves := enumerate_legal_moves s in
        bind (spaceOfList moves)
             (fun m =>
                let s' := execute_move s m in
                (* can we win in one move? *)
                if win_state_dec s' then single (flatMoveToWin m)
                else
                  (* otherwise consider every opposing move in response *)
                  let responses := enumerate_legal_moves s' in
                  (* for each opposing move, obtain a space of counter
                   * strategies and pair them *)
                  let responseSpaces :=
                      map
                        (fun m' =>
                           let s'' := execute_move s' m' in
                           bind (flatStrategySpace n s'')
                                (fun strat => single (m', strat)))
                        responses in
                  (* turn the list of spaces into a space of lists and
                   * use the list of counter strategies to construct
                   * the top-level strategy *)
                  bind (listOfSpacesToSpaceOfLists responseSpaces)
                       (fun l => single (flatRespond m l)))
      end.
  
  Definition solveForStrategy `{Basic} `{Search} (n : nat) (s : state)
    := search (strategySpace n s).
  
End GamePlayer.

Open Scope nat_scope.

Module TicTacToeRules : GameRules.
  Definition move : Set := (nat * nat).
  Inductive shape := X | O.

  Definition opp (s : shape) : shape := match s with X => O | O => X end.
  
  Definition board : Set := list (list (option shape)).
  Definition state : Set := (shape * board).

  Fixpoint update_row (s : shape) (col : nat) (row : list (option shape))
    : list (option shape) :=
    match col with
    | 0 =>
      match row with
      | [] => row (* should not happen: past the end of the row *)
      | h :: t =>
        match h with
        | None => Some s :: t
        | Some _ => row (* should not happen: already a piece there *)
        end
      end
    | S c' =>
      match row with
      | [] => row (* should not happen: past the end of the row *)
      | h :: t => h :: update_row s c' t
      end
    end.

  Fixpoint update_board (s : shape) (row col : nat) (b : board) : board :=
    match row with
    | 0 =>
      match b with
      | [] => b (* should not happen: past the end of the board *)
      | row :: rest =>
        update_row s col row :: rest
      end
    | S r' =>
      match b with
      | [] => b (* should not happen: past the end of the board *)
      | row :: rest =>
        row :: update_board s r' col rest
      end
    end.
  
  Definition execute_move (s : state) (m : move) : state :=
    let ' (x, y) := m in
    let ' (shape, b) := s in
    (* move out of bounds *)
    if ((3 <=? x) || (3 <=? y))%nat then s
    (* update the board, indicate the opposite player *)
    else (opp shape, update_board shape x y b).

  Definition readBoard (x y : nat) (b : board) : option shape :=
    nth y (nth x b []) None.

  Definition rowOneShape (s : shape) (r : nat) (b : board) : Prop :=
    let col0 := readBoard r 0 b in
    let col1 := readBoard r 1 b in
    let col2 := readBoard r 2 b in
    col0 = Some s /\ col1 = Some s /\ col2 = Some s.

  Definition colOneShape (s : shape) (c : nat) (b : board) : Prop :=
    let row0 := readBoard 0 c b in
    let row1 := readBoard 1 c b in
    let row2 := readBoard 2 c b in
    row0 = Some s /\ row1 = Some s /\ row2 = Some s.

  Definition leftDiagonalOneShape (s : shape) (b : board) : Prop :=
    let b00 := readBoard 0 0 b in
    let b11 := readBoard 1 1 b in
    let b22 := readBoard 2 2 b in
    b00 = Some s /\ b11 = Some s /\ b22 = Some s.

  Definition rightDiagonalOneShape (s : shape) (b : board) : Prop :=
    let b02 := readBoard 0 2 b in
    let b11 := readBoard 1 1 b in
    let b20 := readBoard 2 0 b in
    b02 = Some s /\ b11 = Some s /\ b20 = Some s.

  Definition someRowOneShape (s : shape) (b : board) : Prop :=
    rowOneShape s 0 b \/ rowOneShape s 1 b \/ rowOneShape s 2 b.
  Definition someColOneShape (s : shape) (b : board) : Prop :=
    colOneShape s 0 b \/ colOneShape s 1 b \/ colOneShape s 2 b.
  Definition someDiagOneShape (s : shape) (b : board) : Prop :=
    leftDiagonalOneShape s b \/ rightDiagonalOneShape s b.

  Definition winForPlayer (s : shape) (b : board) : Prop :=
    someRowOneShape s b \/ someColOneShape s b \/ someDiagOneShape s b.
  
  (* we will consider X to be the winning player : X wins
   * if some row is all X's, some column is all X's, or
   * a diagonal is all X's *)
  Definition win_state (s : state) : Prop :=
    let ' (_, b) := s in winForPlayer X b.

  Definition shapeEq : eqDec shape.
    constructor. decide equality.
  Defined.

  Definition movEq : eqDec move.
    constructor. decide equality; apply eqDecNat.
  Defined.

  Definition optShapeEq : eqDec (option shape).
    constructor. decide equality. apply shapeEq.
  Defined.

  Definition readBoard_dec : forall (s : shape) (x y : nat) (b : board),
      {readBoard x y b = Some s} + {readBoard x y b <> Some s}.
  Proof.
    intros. apply optShapeEq.
  Defined.
    
  Definition rowOneShape_dec : forall (s : shape) (r : nat) (b : board),
      {rowOneShape s r b} + {~rowOneShape s r b}.
  Proof.
    unfold rowOneShape.
    intros.
    destruct (readBoard_dec s r 0 b);
    destruct (readBoard_dec s r 1 b);
    destruct (readBoard_dec s r 2 b);
    intuition.
  Defined.

  Definition colOneShape_dec : forall (s : shape) (c : nat) (b : board),
      {colOneShape s c b} + {~colOneShape s c b}.
  Proof.
    unfold colOneShape.
    intros.
    destruct (readBoard_dec s 0 c b);
    destruct (readBoard_dec s 1 c b);
    destruct (readBoard_dec s 2 c b);
    intuition.
  Defined.    

  Definition leftDiagonalOneShape_dec : forall (s : shape) (b : board),
      {leftDiagonalOneShape s b} + {~leftDiagonalOneShape s b}.
  Proof.
    intros.
    unfold leftDiagonalOneShape.
    destruct (readBoard_dec s 0 0 b);
    destruct (readBoard_dec s 1 1 b);
    destruct (readBoard_dec s 2 2 b);
    intuition.
  Defined.

  Definition rightDiagonalOneShape_dec : forall (s : shape) (b : board),
      {rightDiagonalOneShape s b} + {~rightDiagonalOneShape s b}.
  Proof.
    intros.
    unfold rightDiagonalOneShape.
    destruct (readBoard_dec s 2 0 b);
    destruct (readBoard_dec s 1 1 b);
    destruct (readBoard_dec s 0 2 b);
    intuition.
  Defined.

  Definition someRowOneShape_dec : forall (s : shape) (b : board),
      {someRowOneShape s b} + {~someRowOneShape s b}.
  Proof.
    intros.
    unfold someRowOneShape.
    destruct (rowOneShape_dec s 0 b);
    destruct (rowOneShape_dec s 1 b);
    destruct (rowOneShape_dec s 2 b);
    intuition.
  Defined.

  Definition someColOneShape_dec : forall (s : shape) (b : board),
      {someColOneShape s b} + {~someColOneShape s b}.
  Proof.
    intros.
    unfold someColOneShape.
    destruct (colOneShape_dec s 0 b);
    destruct (colOneShape_dec s 1 b);
    destruct (colOneShape_dec s 2 b);
    intuition.
  Defined.

  Definition someDiagOneShape_dec : forall (s : shape) (b : board),
      {someDiagOneShape s b} + {~someDiagOneShape s b}.
  Proof.
    intros.
    unfold someDiagOneShape.
    destruct (leftDiagonalOneShape_dec s b);
    destruct (rightDiagonalOneShape_dec s b);
    intuition.
  Defined.
    
  Definition winForPlayer_dec : forall (s : shape) (b : board),
      {winForPlayer s b} + {~winForPlayer s b}.
  Proof.
    intros.
    unfold winForPlayer.
    destruct (someRowOneShape_dec s b);
    destruct (someColOneShape_dec s b);
    destruct (someDiagOneShape_dec s b);
    intuition.
  Defined.

  Definition win_state_dec : forall (s : state), {win_state s} + {~win_state s}.
    intros.
    unfold win_state.
    destruct s.
    destruct (winForPlayer_dec X b); intuition.
  Defined.
  
  Fixpoint allEmptyColumns (row : list (option shape)) (col : nat) : list nat :=
    match row with
    | [] => []
    | h :: t =>
      match h with
      | None => col :: allEmptyColumns t (S col)
      | Some _ => allEmptyColumns t (S col)
      end
    end.

  Fixpoint allEmptySquares (b : board) (r : nat) : list (nat * nat) :=
    match b with
    | [] => []
    | row :: rest =>
      let emptyCols := allEmptyColumns row 0 in
      (map (fun c => (r, c)) emptyCols) ++ (allEmptySquares rest (S r))
    end.
  
  Definition enumerate_legal_moves (s : state) : list move :=
    let ' (shape, board) := s in
    (* if either player has won, there are no legal moves *)
    if (winForPlayer_dec X board) then [] else
      if (winForPlayer_dec O board) then [] else
        allEmptySquares board 0.
End TicTacToeRules.

Open Scope Z.

Module ChessRules : GameRules.

  Instance coordEq : eqDec (Z * Z).
    constructor. decide equality; apply eqDecZ.
  Defined.

  Inductive piece := King | Queen | Bishop | Knight | Rook | Pawn.
  Inductive color := White | Black.

  Instance colorEq : eqDec color.
    constructor. decide equality.
  Defined.

  Instance pieceEq : eqDec piece.
    constructor. decide equality.
  Defined.
  
  (* moves are "move piece at (x1, y1) to (x2, y2)" *)
  Definition move : Set := (piece * (Z * Z) * (Z * Z)).
  Definition movEq : eqDec move.
    constructor. 
    decide equality; apply eqDecProd.
  Defined.

  Definition board : Set := (list (list (option (color * piece)))).

  (* this board is represented as a list of lists, where the first few 
   * lists are the "top" of the board, meaning (0, 0). is the 
   * leftmost position in the top row. However, the board is traditionally 
   * described so that white's starting rows are below (1 and 2) and 
   * black's are above (7 and 8), we "invert" x when we index into 
   * the board *)
  Definition invertX (x : nat) : nat := (7 - x)%nat.
  
  Definition lookUpCoord (x y : nat) (b : board) : option (color * piece) :=
    (nth y (nth (invertX x) b []) None).

  Fixpoint replaceNth {A} (l : list A) (n : nat) (a : A) : list A :=
    match n with
    | O =>
      match l with
      | [] => l (* should not happen *)
      | h :: t => a :: t
      end
    | S n' =>
      match l with
      | [] => l (* should not happen *)
      | h :: t => h :: replaceNth t n' a
      end
    end.
  
  Definition replaceCoord (x y : nat) (b : board) (p : option (color * piece))
    : board :=
    if (x <? 8)%nat && (y <? 8)%nat then
      let row := nth (invertX x) b [] in
      replaceNth b (invertX x) (replaceNth row y p)
    else b. (* not in bounds, do nothing *)
  
  (* state: board, color of player to move, coords of white king, coords
   *        of black king *)
  Definition state : Set := (board * color * (Z * Z) * (Z * Z)).

  Definition inBounds (coord : Z * Z) : bool:=
    let ' (x, y) := coord in
    (0 <=? x)%Z && (0 <=? y)%Z && (x <? 8)%Z && (y <? 8)%Z.

  (* we can express most pieces' movement as a union of traversals *)
  (* traversal: given a function to get the next coordinate, move on for
   * up to some bound, stopping after either hitting a friendly piece
   * (cannot capture), capturing one enemy (cannot keep going), or
   * hitting the boundary *)
  Fixpoint traversal_helper
             (bound : nat)
             (b : board) (c : color)
             (coord : Z * Z)
             (next : Z * Z -> Z * Z)
             (acc : list (Z * Z))
             (skipStart : bool)
    : list (Z * Z) :=
    if (negb (inBounds coord)) then acc
    else
      let ' (x, y) := coord in
      let ' (acc', keepGoing) :=
          if skipStart then (acc, true)
          else match (lookUpCoord (Z.to_nat x) (Z.to_nat y) b) with
               | None =>
                 (* space is empty, so we can go here *)
                 ((x, y) :: acc, true)
               | Some (c', p) =>
                 if eqDecide c c'
                 then (* colors match, so cannot capture *)
                   (acc, false)
                 else (* can capture enemy piece, but must stop *)
                   ((x, y) :: acc, false)
               end
      in
      match bound with
      | O => acc'
      | S n =>
        let nextCoord := next coord in
        if (keepGoing && inBounds nextCoord) then
          traversal_helper n b c nextCoord next acc' false
        else acc'
      end.

  Fixpoint unionOfTraversals
           (bound : nat)
           (b : board)
           (c : color)
           (coord : Z * Z)
           (traversals : (list (Z * Z -> Z * Z)))
           (acc : list (Z * Z))
    : list (Z * Z) :=
    match traversals with
    | h :: t =>
      unionOfTraversals
        bound b c coord t (traversal_helper bound b c coord h acc true)
    | [] => acc
    end.

  Definition traverseUp (coord : Z * Z) : Z * Z :=
    let ' (x, y) := coord in (x + 1, y).
  Definition traverseDown (coord : Z * Z) : Z * Z :=
    let ' (x, y) := coord in (x - 1, y).
  Definition traverseLeft (coord : Z * Z) : Z * Z :=
    let ' (x, y) := coord in (x, y - 1).
  Definition traverseRight (coord : Z * Z) : Z * Z :=
    let ' (x, y) := coord in (x, y + 1).
  Definition traverseLeftDiagUp (coord : Z * Z) : Z * Z :=
    let ' (x, y) := coord in (x + 1, y - 1).
  Definition traverseLeftDiagDown (coord : Z * Z) : Z * Z :=
    let ' (x, y) := coord in (x - 1, y - 1).
  Definition traverseRightDiagUp (coord : Z * Z) : Z * Z :=
    let ' (x, y) := coord in (x + 1, y + 1).
  Definition traverseRightDiagDown (coord : Z * Z) : Z * Z :=
    let ' (x, y) := coord in (x - 1, y + 1).

  Definition cardinalDirections :=
    [traverseUp; traverseDown; traverseLeft; traverseRight].
  Definition diagonalDirections :=
    [traverseLeftDiagUp; traverseLeftDiagDown;
       traverseRightDiagDown; traverseRightDiagUp].
  Definition allDirections := cardinalDirections ++ diagonalDirections.

  (* pawn start row is relevant for determining if the pawn can charge
   * ahead two spaces (and en pessant, though we do not implement it *)
  Definition pawnStartingRow (c : color) : Z :=
    match c with
    | Black => 6
    | White => 1
    end.

  (* pawns promote when they reach the end of the board *)
  Definition pawnEndRow (c : color) : Z :=
    match c with
    | Black => 0
    | White => 7
    end.

  Definition canCapture (b : board) (c : color) (coord : Z * Z) : bool:=
    let ' (x, y) := coord in
    match (lookUpCoord (Z.to_nat x) (Z.to_nat y) b) with
    | None => false
    | Some (c', _) => if eqDecide c c' then false else true
    end.

  Definition empty (b : board) (coord : Z * Z) : bool:=
    let ' (x, y) := coord in
    match (lookUpCoord (Z.to_nat x) (Z.to_nat y) b) with
    | None => true
    | Some _ => false
    end.

  (* knights skip over pieces, but need to see if destination is valid *)
  Definition knightMoves (b : board) (c : color) (start : Z * Z)
    : list (Z*Z) :=
    let '(x, y) := start in
    let candidates := [(x + 2, y + 1); (x + 2, y - 1);
                        (x - 2, y + 1); (x - 2, y - 1);
                          (x + 1, y + 2); (x + 1, y - 2);
                            (x - 1, y + 2); (x - 1, y - 2)] in
    filter
      (fun coord => inBounds coord && (empty b coord || canCapture b c coord))
      candidates.

  Definition pawnMoves (b : board) (c : color) (start : Z * Z)
    : list (Z * Z) :=
    let ' (x, y) := start in
    let direction := (match c with Black => -1 | White => 1 end) in
    let moveCandidates :=
        if inBounds (x + direction, y) && empty b (x + direction, y) then
          [(x + direction, y)] else [] in
    (* pawn can move two spaces if they are free and they are in the starting
     * row *)
    let moveCandidates' :=
        if (x =? pawnStartingRow c)
             && (empty b (x + direction, y))
             && (empty b (x + 2*direction, y))
        then
          (x + 2*direction, y) :: moveCandidates else moveCandidates in
    (* pawn can move diagonally if it can capture *)
    let captureCandidates :=
        filter (fun coord => inBounds coord && canCapture b c coord)
               [(x + direction, y - 1); (x + direction, y + 1)] in
    moveCandidates' ++ captureCandidates.     
  
  Definition reachableSquares (b : board) (source : (color * piece * Z * Z))
    : list (Z * Z) :=
    let ' (c, p, x, y) := source in
    match p with
    | King => unionOfTraversals 1 b c (x, y) allDirections []
    | Queen => unionOfTraversals 8 b c (x, y) allDirections []
    | Bishop => unionOfTraversals 8 b c (x, y) diagonalDirections []
    | Rook => unionOfTraversals 8 b c (x, y) cardinalDirections []
    | Knight => knightMoves b c (x, y)
    | Pawn => pawnMoves b c (x, y)
    end.
 
  Fixpoint existsbWithIndex {A} (f : Z -> A -> bool) (l : list A) : bool:=
    let aux :=
        (fix helper (f : Z -> A -> bool) (l : list A) (z : Z) : bool :=
           match l with
           | [] => false
           | h :: t =>
             if f z h then true else helper f t (z + 1)
           end)
    in aux f l 0.

  Fixpoint mapWithIndex {A} {B}
           (f : Z -> A -> B) (l : list A) : list B :=
    let aux :=
        (fix helper f l z :=
           match l with
           | [] => []
           | h :: t =>
             f z h :: helper f t (z + 1)
           end)
    in aux f l 0.

  Definition invertX' (x : Z) : Z := 7 - x.
  
  Definition canBeCaptured (b : board) (c : color) (coord : (Z * Z)) : bool:=
    existsbWithIndex
      (fun x row =>
         let x' := invertX' x in
         existsbWithIndex
         (fun y p =>
           match p with
           | None => false
           | Some (c', p') =>
             (* our reachability check takes into account capturing *)
             if In_dec eqDecide coord (reachableSquares b (c', p', x', y))
             then true else false
           end) row) b.

  (* lists all pieces of a given color with their coordinates *)
  Definition allPieces (b : board) (c : color)
    : list (color * piece * Z * Z) :=
    let candidates :=
        mapWithIndex
          (fun x row =>
             let x' := invertX' x in
             mapWithIndex
               (fun y p =>
                  match p with
                  | None => None
                  | Some (c', p') =>
                    if eqDecide c c'
                    then Some (c', p', x', y)
                    else None
                  end) row) b in
    let flattened := fold_right (fun acc r => r ++ acc) [] candidates in
    fold_right
      (fun p acc =>
         match p with
         | None => acc
         | Some c => c :: acc
         end) [] flattened.

  (* check: can the king be captured? *)
  Definition inCheck (s : state) (c : color) : bool:=
    let ' (b, _, kb, kw) := s in
    match c with
    | Black => canBeCaptured b c kb
    | White => canBeCaptured b c kw
    end.

  (* this will assume the move is legal *)
  Definition execute_move (s : state) (m : move) : state :=
    let ' (b, c, kb, kw) := s in
    let ' (p, (x1, y1), (x2, y2)) := m in
    let x1n := Z.to_nat x1 in
    let x2n := Z.to_nat x2 in
    let y1n := Z.to_nat y1 in
    let y2n := Z.to_nat y2 in
    let opp := (match c with Black => White | White => Black end) in
    match (lookUpCoord (Z.to_nat x1) (Z.to_nat y1) b) with
    | None => (b, opp, kb, kw) (* no piece to move, should not happen *)
    | Some (c', _) =>
      if eqDecide c c'
      (* moving piece of our color *)
      then
        (* new board: replace current piece coord with nothing,
         * place it in its new position *)
        let removePiece := (replaceCoord x1n y1n b None) in
        (* pawn promotion: if a pawn has hit its end row, replace with a 
         * queen (simplified from actual rule, which lets the player choose
         * from any piece besides king) *)
        let p' := (match p with
                   | Pawn => if eqDecide x2 (pawnEndRow c) then Queen else p
                   | _ => p
                  end) in
        let newBoard := (replaceCoord x2n y2n removePiece (Some (c, p'))) in
        (* if we've moved the king, then update the appropriate coordinate *)
        if eqDecide p King then
          match c with
          | Black => (newBoard, opp, (x2, y2), kw)
          | White => (newBoard, opp, kb, (x2, y2))
          end
        else (newBoard, opp, kb, kw)
      (* wrong color, shouldn't happen *)
      else (b, opp, kb, kw)
    end.

  Definition enumerate_legal_moves (s : state) : list move :=
    let ' (b, c, kb, kw) := s in
    let pieces := allPieces b c in
    (* all possible moves: append together the reachable spaces
     * from each piece *)
    let allMoves : list move :=
        fold_right
          (fun p acc =>
             let ' (_, p', x, y) := p in
             let reachable := reachableSquares b p in
             map (fun s => (p', (x, y), s)) reachable ++ acc)
          [] pieces in
    (* if the player is in check, then the only legal moves are those
     * which take the player out of check *)
    if inCheck s c
    then filter (fun m => negb (inCheck (execute_move s m) c)) allMoves
    else allMoves.

  (* white wins if black is in check and has no legal moves *)
  Definition win_state (s : state) : Prop :=
    let ' (b, _, kb, kw) := s in
    inCheck s Black = true /\ enumerate_legal_moves (b, Black, kb, kw) = [].

  Definition win_state_dec : forall (s : state), {win_state s} + {~win_state s}.
    intros.
    unfold win_state.
    destruct (inCheck s Black); destruct s; do 2 (destruct p).
    * destruct (enumerate_legal_moves (b, Black, p1, p0)).
      + left. intuition.
      + right. intro H. destruct H. congruence.
    * right. intro H. destruct H. congruence.
  Defined.
        
End ChessRules.

Open Scope nat_scope.

Module ConnectFourRules : GameRules.
  Definition move : Set := nat. (* move = drop down column *)
  Instance movEq : eqDec move.
    apply eqDecNat.
  Defined.
  
  Inductive color := Red | Black.
  Instance colorEq : eqDec color.
    constructor. decide equality.
  Defined.

  Definition opp (c : color) : color :=
    match c with Red => Black | Black => Red end.

  (* list of columns *)
  Definition board : Set := list(list(option color)).
  
  (* state: which player is moving, also the board *)
  Definition state : Set := (color * board)%type.

  Definition num_rows : nat := 6.
  Definition num_cols : nat := 7.

  Definition x_bound : nat := num_rows - 1.
  Definition y_bound : nat := num_cols - 1.
  
  (* bottom of board is x coordinate of 0, but comes at end of list *)
  Definition invertX (x : nat) : nat := x_bound - x.

  Definition inBounds (x y : nat) : bool :=
    (x <? num_rows)%nat && (y <? num_cols)%nat.
  
  Definition lookUpCoord (b : board) (x y : nat) : option color :=
    let col := nth y b [] in nth (invertX x) col None.

  Definition colOpen (col : list (option color)) : bool :=
    match col with
    | [] => false
    | h :: t =>
      match h with
      | None => true
      | _ => false
      end
    end.
  
  Fixpoint dropCol (c : color) (col : list (option color))
    : list (option color) :=
    match col with
    | [] => col (* should not happen *)
    | h :: t =>
      match h with
      | Some c' => col (* should not happen *)
      | None =>
        match t with
        | [] => [Some c] (* end of the column, we're done *)
        | h' :: t' =>
        (* do we have room to fall more? *)
          match h' with
          | Some c' => Some c :: h' :: t (* no *)
          | None => h' :: dropCol c t (* fall more with lookahead *)
          end
        end
      end
    end.

  Fixpoint replaceCol (b : board) (col : list (option color)) (y : nat)
    : board :=
    match b with
    | [] => b (* should not happen *)
    | h :: t =>
      match y with
      | O => col :: t
      | S y' =>
        h :: replaceCol t col y'
      end
    end.
  
  Definition dropPiece (b : board) (c : color) (y : nat) : board :=
    let col := nth y b [] in
    replaceCol b (dropCol c col) y.

  Definition listMatchesColor (c : color) (l : list (option color)) : bool:=
    forallb (fun oc => match oc with
                    | None => false
                    | Some c' =>
                      if eqDecide c c' then true else false
                    end) l.

  Fixpoint zip {A} {B} (l1 : list A) (l2 : list B) : list (A * B) :=
    match l1 with
    | h :: t =>
      match l2 with
      | h' :: t' =>
        (h, h') :: zip t t'
      | [] => []
      end
    | [] => []
    end.
  
  Definition checkCoordsForMatch
             (b : board) (c : color) (xs : list nat) (ys : list nat) : bool :=
    listMatchesColor c
      (map (fun p => let ' (x, y) := p in lookUpCoord b x y) (zip xs ys)).

  Definition sameCoord (c : nat) : list nat := [c; c; c; c].
  Definition decreasing (c : nat) : list nat := [c; c - 1; c - 2; c - 3].
  Definition increasing (c : nat) : list nat := [c; c + 1; c + 2; c + 3].

  Definition roomToDecrease (start : nat) : bool := negb (start <? 3).
  Definition roomToIncrease (bound : nat) (start : nat) : bool :=
    (start <? bound - 2).

  Definition fourRight (b : board) (c : color) (x y : nat) : bool :=
    if (roomToIncrease y_bound y && (inBounds x y)) then
      checkCoordsForMatch b c (sameCoord x) (increasing y)
    else false.
  Definition fourUp (b : board) (c : color) (x y : nat) : bool:=
    if (roomToIncrease x_bound x && (inBounds x y)) then
      checkCoordsForMatch b c (increasing x) (sameCoord y)
    else false.
  Definition rightDiagonalUp (b : board) (c : color) (x y : nat) : bool :=
    if (roomToIncrease x_bound x
                       && roomToIncrease y_bound y && (inBounds x y))
    then checkCoordsForMatch b c (increasing x) (increasing y)
    else false.
  Definition rightDiagonalDown (b : board) (c : color) (x y : nat) : bool :=
    if (roomToIncrease y_bound y
                       && roomToDecrease x && (inBounds x y))
    then checkCoordsForMatch b c (decreasing x) (increasing y)
    else false.

  Fixpoint countUp (n : nat) : list nat :=
    match n with
    | O => []
    | S n' => n' :: countUp n'
    end.

  Fixpoint allPairs {A} {B} (l1 : list A) (l2 : list B) : list (A*B) :=
    match l1 with
    | [] => []
    | a :: t => (map (fun b => (a, b)) l2) ++ allPairs t l2
    end.

  (* we can check for victory by only scanning right,
   * checking for rightward horizontal four's, upward four's,
   * right upward diagonal four's, and right downward diagonal four's
   * (any downward four is an upward four; any left diagonal is also
   *  a right diagonal in the other direction; any left horizontal
   *  four is a right horizontal four) *)
  Definition winForPlayer (b : board) (c : color) : bool:=
    let allRows := countUp num_rows in
    let allCols := countUp num_cols in
    let rightwardFour :=
        existsb (fun p => let ' (x, y) := p in
                       fourRight b c x y)
                (allPairs
                   allRows
                   (filter (roomToIncrease y_bound) allCols)) in
    let upwardFour :=
        existsb (fun p => let ' (x, y) := p in
                       fourUp b c x y)
                (allPairs
                   (filter (roomToIncrease x_bound) allRows)
                   allCols) in
    let upDiagFour :=
        existsb (fun p => let ' (x, y) := p in
                       rightDiagonalUp b c x y)
                (allPairs
                   (filter (roomToIncrease x_bound) allRows)
                   (filter (roomToIncrease y_bound) allCols)) in
    let downDiagFour :=
        existsb (fun p => let ' (x, y) := p in
                       rightDiagonalDown b c x y)
                (allPairs
                   (filter roomToDecrease allRows)
                   (filter (roomToIncrease y_bound) allCols)) in
    rightwardFour || upwardFour || upDiagFour || downDiagFour.
    
  (* win for red *)
  Definition win_state (s : state) : Prop :=
    let ' (_, b) := s in winForPlayer b Red = true.

  Definition win_state_dec : forall (s : state), {win_state s} + {~win_state s}.
    intros. unfold win_state. destruct s.
    destruct (winForPlayer b Red); auto.
  Defined.

  Definition execute_move (s : state) (m : move) : state :=
    let ' (c, b) := s in
    (* is the column in bounds? if not, do nothing *)
    if (m <? num_cols) then
      (* is there an opening in the column? if not, do nothing *)
      if (colOpen (nth m b [])) then
        (* update the board and switch the color *)
        (opp c, dropPiece b c m)
      else (opp c, b)
    else (opp c, b).
  
  Definition enumerate_legal_moves (s : state) : list move :=
    let ' (c, b) := s in
    (* no legal moves if a player has won *)
    if (winForPlayer b Red || winForPlayer b Black) then []
    else
      (* otherwise you can drop a piece down any open column *)
      let allCols := countUp num_cols in
      filter (fun c => colOpen (nth c b [])) allCols.
End ConnectFourRules.

Module TicTacToePlayer := GamePlayer(TicTacToeRules).
Module ChessPlayer := GamePlayer(ChessRules).
Module ConnectFourPlayer := GamePlayer(ConnectFourRules).

Require Import Rosette.Quantified.

Section TicTacToeSolver.
  Import TicTacToeRules.
  Import TicTacToePlayer.

  Definition solveTicTacToeGame (s : state) (n : nat)
    : option (Result flatStrategy).
    destruct (solveForStrategy n s).
    (* search returns an example *)
    * refine (Some (solution (flattenStrat s a))).
    (* search is empty *)
    * refine (Some uninhabited).
    (* search is unknown *)
    * refine None.
  Defined.
End TicTacToeSolver.

Extraction Language Scheme.

Extraction "ticTacToe" solveTicTacToeGame.

Section ChessSolver.
  Import ChessRules.
  Import ChessPlayer.

  Definition solveChessGame (s : state) (n : nat)
    : option (Result flatStrategy).
    destruct (solveForStrategy n s).
    * refine (Some (solution (flattenStrat s a))).
    * refine (Some uninhabited).
    * refine None.
  Defined.
End ChessSolver.

Extraction Language Scheme.

Extraction "chess" solveChessGame.

Section ConnectFourSolver.
  Import ConnectFourRules.
  Import ConnectFourPlayer.

  Definition solveConnectFourGame (s : state) (n : nat)
    : option (Result flatStrategy).
    destruct (solveForStrategy n s).
    * refine (Some (solution (flattenStrat s a))).
    * refine (Some uninhabited).
    * refine None.
  Defined.
End ConnectFourSolver.

Extraction Language Scheme.

Extraction "connectFour" solveConnectFourGame.