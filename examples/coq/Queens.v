Require Import Basic.
Require Import Rosette.Quantified.
Require Import ListEx.
Require Import Native.
Require Import Bool.
Require Import Arith.EqNat.
Require Import Integer.
Require Import EqDec.
Require Import ZArith.
Require Import BinInt.
Require Import ZProperties.
Require Import Bool.
Require Import Logic.Classical_Pred_Type.
Require Import Logic.Classical_Prop.
Require Import Permutation.
Require Import Coq.Sorting.Mergesort.

Existing Instance rosetteBasic.
Existing Instance rosetteSearch.

Definition elem {A} `{eqDec A} (a:A) : list A -> bool :=
  existsb (fun a' => if a =? a' then true else false).

Fixpoint distinct {A} `{eqDec A} (l:list A) : bool :=
  match l with
  | a :: l => andb (negb (elem a l)) (distinct l)
  | [] => true
  end.

Definition uncurry {A B C} (f:A->B->C) (ab:A*B) : C :=
  f (fst ab) (snd ab).

Fixpoint nListSpace `{Basic} {A} (s:Space A) (n:nat) : Space (list A) :=
  match n with
  | 0%nat => single []
  | S n => bind (nListSpace s n) (fun l => 
          bind s (fun a => single (a :: l)))
  end.

Definition index {A} : list A -> list (A * Int) :=
  let fix rec n l :=
    match l with
    | [] => []
    | a::l => (a,n) :: rec (plus one n) l
    end 
  in rec zero.

Definition isLegal (queens : list (Int * Int)) : bool :=
  forallb (fun x => x) [
    distinct (map fst queens);
    distinct (map snd queens);
    distinct (map (uncurry plus) queens);
    distinct (map (uncurry minus) queens)
  ].

Definition solveNQueens (n:nat) : Result (list (Int * Int)).
  refine (search 
    (bind (nListSpace (range zero (natToInt n)) n)
      (fun xs:list Int => _))).
  refine (let ps := index xs in _).
  refine (if isLegal ps then single ps else empty).
Defined.

Extraction Language Scheme.

Extraction "queens" solveNQueens.

(* Proofs of completation and soundness for solution *)

Definition collision (p1 p2 : Z * Z) : Prop :=
  let ' (x1, y1) := p1 in
  let ' (x2, y2) := p2 in
    (* x1 = x2 => queens are in the same row *)
    (* y1 = y2 => queens are in the same column *)
    (* |x2 - x1| = |y2 - y1| => queens are in the same diagonal *)
    (x1 = x2) \/ (y1 = y2) \/ (Zabs (x1 - x2) = Zabs (y1 - y2)).

Definition ith (i : nat) (l : list (Z*Z)) := nth i l (0, 0).

Definition distinctIndices {A} (i j : nat) (l : list A) : Prop :=
  (i < length l)%nat /\ (j < length l)%nat /\ i <> j.

Definition inBounds (p : Z * Z) (n : nat) : Prop :=
  let '(x, y) := p in
  0 <= x < Z.of_nat n /\ 0 <= y < Z.of_nat n.

Definition noCollisions (positions : list (Z*Z)) : Prop :=
  forall (i j : nat), distinctIndices i j positions
               -> ~collision (ith i positions) (ith j positions).

Definition allInBounds (positions : list (Z*Z)) : Prop :=
  forall (p : Z*Z), In p positions -> inBounds p (length positions).

Definition correct (n : nat) (positions : list (Z*Z)) : Prop :=
  length positions = n /\ allInBounds positions /\ noCollisions positions.

Lemma diagonalOptimization : forall (x1 x2 y1 y2 : Z),
    Zabs (x1 - x2) = Zabs (y1 - y2)
    <-> ((x1 + y1) = (x2 + y2) \/ (x1 - y1) = (x2 - y2)).
Proof.
  intros.
  split; intros.
  * apply Z.abs_eq_cases in H.
    destruct H; omega.
  * destruct H as [H | H].
    + assert (x1 - x2 = y2 - y1) by omega.
      assert (Z.abs (x1 - x2) = Z.abs (y2 - y1)) by (rewrite H0; reflexivity).
      assert (-(y2 - y1) = y1 - y2) by omega.
      assert (Z.abs (y2 - y1) = Z.abs (y1 - y2))
        by (rewrite <- H2; symmetry; apply Z.abs_opp).      
      rewrite H3 in H1. assumption.
    + assert (x1 - x2 = y1 - y2) by omega.
      rewrite H0. reflexivity.
Qed.

Definition collision' (p1 p2 : Z * Z): Prop :=
  match p1, p2 with
    (x1, y1), (x2, y2) =>
    (x1 = x2) \/ (y1 = y2) \/ (x1 + y1) = (x2 + y2) \/ (x1 - y1) = (x2 - y2)
  end.

Lemma collisionEquiv : forall (p1 p2 : Z * Z), collision p1 p2 <-> collision' p1 p2.
Proof.
  intros. unfold collision. unfold collision'.
  destruct p1 as [x1 y1]. destruct p2 as [x2 y2].
  split; intros.
  * destruct H; intuition.
    apply diagonalOptimization in H0.
    destruct H0; intuition.
  * destruct H; intuition;
    do 2 (do 2 right; apply diagonalOptimization; intuition).
Qed.

Definition noCollisions' (positions : list (Z*Z)) : Prop :=
  ~exists (i j : nat), distinctIndices i j positions
                /\ collision (ith i positions) (ith j positions).

Lemma collisionsEquiv : forall (positions : list (Z*Z)),
    noCollisions positions <-> noCollisions' positions.
Proof.
  intros. unfold noCollisions. unfold noCollisions'.
  split; intros.
  * apply all_not_not_ex. intros. apply all_not_not_ex. intros.
    intro Hn. firstorder.
  * intro H'. apply H.
    exists i. exists j. firstorder.
Qed.

Definition existsCollision (positions : list (Z*Z)) : Prop :=
  exists (i j : nat), distinctIndices i j positions
               /\ collision (ith i positions) (ith j positions).
  
Lemma existsCollisionNot : forall (positions : list (Z*Z)),
    existsCollision positions <-> ~noCollisions positions.
Proof.
  intros. unfold existsCollision. unfold noCollisions.
  split; intros.
  * intro H'. apply collisionsEquiv in H'. unfold noCollisions' in H'.
    contradiction.
  * apply not_all_ex_not in H. destruct H.
    apply not_all_ex_not in H. destruct H.
    apply imply_to_and in H. destruct H.
    apply NNPP in H0.
    exists x. exists x0. firstorder.
Qed.

Definition forSomePairAlike (positions : list (Z*Z))
           (quantity : (Z*Z) -> Z) : Prop :=
  exists (i j: nat), distinctIndices i j positions
              /\ quantity (ith i positions) = quantity (ith j positions).

Lemma xAlikeCollision : forall (positions : list (Z*Z)),
    forSomePairAlike positions (fun p => fst p)
    -> existsCollision positions.
Proof.
  unfold existsCollision. unfold forSomePairAlike. intros.
  destruct H. destruct H.
  exists x. exists x0. split; try intuition.
  unfold collision.
  remember (ith x positions) as p1.
  remember (ith x0 positions) as p2.
  destruct p1 as [x1 y1]. destruct p2 as [x2 y2].
  simpl in H1. intuition.
Qed.

Lemma yAlikeCollision : forall (positions : list (Z*Z)),
    forSomePairAlike positions (fun p => snd p)
    -> existsCollision positions.
Proof.
  unfold existsCollision. unfold forSomePairAlike. intros.
  destruct H. destruct H.
  exists x. exists x0. split; try intuition.
  unfold collision.
  remember (ith x positions) as p1.
  remember (ith x0 positions) as p2.
  destruct p1 as [x1 y1]. destruct p2 as [x2 y2].
  simpl in H1. intuition.
Qed.

Lemma sumAlikeCollision : forall (positions : list (Z*Z)),
    forSomePairAlike positions (fun p => fst p + snd p)
    -> existsCollision positions.
Proof.
  unfold existsCollision. unfold forSomePairAlike. intros.
  do 2 (destruct H).
  exists x. exists x0. split; try intuition.
  unfold collision.
  remember (ith x positions) as p1.
  remember (ith x0 positions) as p2.
  destruct p1 as [x1 y1]. destruct p2 as [x2 y2].
  simpl in H1. right. right.
  apply diagonalOptimization.
  firstorder.
Qed.

Lemma diffAlikeCollision : forall (positions : list (Z*Z)),
    forSomePairAlike positions (fun p => fst p - snd p)
    -> existsCollision positions.
Proof.
  unfold existsCollision. unfold forSomePairAlike. intros.
  do 2 (destruct H).
  exists x. exists x0. split; try intuition.
  unfold collision.
  remember (ith x positions) as p1.
  remember (ith x0 positions) as p2.
  destruct p1 as [x1 y1]. destruct p2 as [x2 y2].
  simpl in H1. right. right.
  apply diagonalOptimization.
  firstorder.
Qed.

Lemma alikeIfCollision : forall (positions : list (Z*Z)),
    existsCollision positions ->
    forSomePairAlike positions (fun p => fst p)
    \/ forSomePairAlike positions (fun p => snd p)
    \/ forSomePairAlike positions (fun p => fst p + snd p)
    \/ forSomePairAlike positions (fun p => fst p - snd p).
Proof.
  unfold existsCollision. unfold forSomePairAlike.
  intros. do 2 (destruct H). destruct H as [H H'].
  unfold collision in H'.
  remember (ith x positions) as p1.
  remember (ith x0 positions) as p2.
  destruct p1 as [x1 y1]. destruct p2 as [x2 y2].
  destruct H'; [left | right; destruct H0;
                       [left | right;
                               apply diagonalOptimization in H0;
                               destruct H0; [left | right]]];
  (exists x; exists x0; rewrite <- Heqp1; rewrite <- Heqp2; intuition).
Qed.

Theorem collisionIffAlike : forall (positions : list (Z*Z)),
    existsCollision positions <->
    forSomePairAlike positions (fun p => fst p)
    \/ forSomePairAlike positions (fun p => snd p)
    \/ forSomePairAlike positions (fun p => fst p + snd p)
    \/ forSomePairAlike positions (fun p => fst p - snd p).
Proof.
  intros. split; intros.
  * apply alikeIfCollision; auto.
  * destruct H; [| destruct H; [| destruct H]].
    - apply xAlikeCollision. assumption.
    - apply yAlikeCollision. assumption.
    - apply sumAlikeCollision. assumption.
    - apply diffAlikeCollision. assumption.
Qed.

Definition distinct' {A} (l : list A) : Prop :=
  forall (i j : nat) (d : A), distinctIndices i j l -> nth i l d <> nth j l d.

Lemma distinctIndicesTransfer {A B} :
  forall (l1 : list A) (l2 : list B) (i j : nat),
    length l1 = length l2 ->
    (distinctIndices i j l1 <-> distinctIndices i j l2).
Proof. intros. unfold distinctIndices. split; intuition. Qed.

Lemma notAlikeIffDistinct :
  forall (positions : list (Z*Z)) (quantity : (Z*Z) -> Z),
    distinct' (map quantity positions)
    <-> ~forSomePairAlike positions quantity.
Proof.
  intros. unfold distinct'. unfold forSomePairAlike.
  split; intros.
  * intro H'. destruct H'. do 2 (destruct H0).
    remember (nth x (map quantity positions) 0) as p1.
    remember (nth x0 (map quantity positions) 0) as p2.
    assert (length (map quantity positions) = length positions)
      by apply map_length.
    apply distinctIndicesTransfer with (i := x) (j := x0) in H2.
    assert (distinctIndices x x0 (map quantity positions))
      by intuition.
    apply H with (d := 0) in H3.
    apply H3.
    unfold ith in H1.
    assert (nth x (map quantity positions) 0
            = nth x (map quantity positions) (quantity (0, 0)))
           by (apply nth_indep; apply H2 in H0;
               unfold distinctIndices in H0; intuition).
    assert (nth x0 (map quantity positions) 0
            = nth x0 (map quantity positions) (quantity (0, 0)))
      by (apply nth_indep; apply H2 in H0;
          unfold distinctIndices in H0; intuition).
    rewrite H4. rewrite H5.
    rewrite map_nth. rewrite map_nth.
    assumption.
  * apply not_ex_all_not with (n := i) in H.
    apply not_ex_all_not with (n := j) in H.
    apply not_and_or in H.
    destruct H.
    + assert (length (map quantity positions) = length positions)
        by apply map_length.
      apply distinctIndicesTransfer with (i0 := i) (j0 := j) in H1.
      apply H1 in H0. contradiction.
    + intro H'. apply H.
      assert (nth i (map quantity positions) d
              = nth i (map quantity positions) (quantity (0, 0)))
        by (apply nth_indep; unfold distinctIndices in H0; intuition).
      assert (nth j (map quantity positions) d
              = nth j (map quantity positions) (quantity (0, 0)))
        by (apply nth_indep; unfold distinctIndices in H0; intuition).
      rewrite H1 in H'. rewrite H2 in H'. clear H1. clear H2.
      unfold ith.
      rewrite map_nth in H'. rewrite map_nth in H'. assumption.
Qed.

Theorem noCollisionsIffDistinct : forall (positions : list (Z*Z)), 
    noCollisions positions
    <-> distinct' (map (fun p => fst p) positions)
      /\ distinct' (map (fun p => snd p) positions)
      /\ distinct' (map (fun p => fst p + snd p) positions)
      /\ distinct' (map (fun p => fst p - snd p) positions).
Proof.
  intros. split; intros.
  * apply collisionsEquiv in H.
    split; [| split; [| split]];
      (apply notAlikeIffDistinct; intro H';
       assert (existsCollision positions)
         by (apply collisionIffAlike; intuition);
       contradiction).
  * destruct H as [Hx H1]. destruct H1 as [Hy H2]. destruct H2 as [Hs Hd].
    apply collisionsEquiv. unfold noCollisions'. intro H.
    apply notAlikeIffDistinct in Hx.
    apply notAlikeIffDistinct in Hy.
    apply notAlikeIffDistinct in Hs.
    apply notAlikeIffDistinct in Hd.
    do 3 (destruct H).
    unfold collision in H0. unfold forSomePairAlike in *.
    remember (ith x positions) as p1.
    remember (ith x0 positions) as p2.
    destruct p1 as [x1 y1]. destruct p2 as [x2 y2].
    destruct H0; [apply Hx |
      destruct H0; [apply Hy |
        apply diagonalOptimization in H0;
        destruct H0; [apply Hs | apply Hd]]];
    (exists x; exists x0; rewrite <- Heqp1; rewrite <- Heqp2; split; intuition).
Qed.

Lemma existsb_false {A} : forall (l : list A) (f : A -> bool),
    existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
  intros. split; intros.
  * induction l.
    + inversion H0.
    + simpl in H. apply orb_false_iff in H. destruct H.
      simpl in H0. destruct H0; intuition.
      rewrite <- H0. assumption.
  * induction l.
    + reflexivity.
    + simpl. apply orb_false_iff. split.
      - apply H. intuition.
      - apply IHl. intros. simpl in H. apply H. intuition.
Qed.

Lemma In_nth_cons {A} : forall (a d : A) (l : list A) (i : nat),
    (i < length l)%nat -> (nth i l d) <> a ->
    In (nth (S i) (a :: l) d) (a :: l) -> In (nth i l d) l.
Proof.
  intros.
  simpl in H1.
  destruct H1.
  * symmetry in H1. contradiction.
  * assumption.
Qed.

Theorem distinctComputation {A} `{eqDec A} : forall (l : list A),
    distinct l = true <-> distinct' l.
Proof.
  intros. unfold distinct'. split.
  * induction l; intros; unfold distinctIndices in H1.
    + destruct H1. inversion H1.
    + simpl in H0. apply andb_true_iff in H0. destruct H0.
      destruct i; destruct j.
      - simpl. destruct H1. destruct H3. exfalso. apply H4. reflexivity.
      - simpl. apply negb_true_iff in H0. unfold elem in H0.
        assert (forall x, In x l -> (if eqDecide a x then true else false) = false)
          by (apply existsb_false; assumption).
        destruct H1.
        destruct H4.
        assert ((j < length l)%nat) by intuition.
        assert (In (nth j l d) l) by (apply nth_In; assumption).
        apply H3 in H7.
        destruct (eqDecide a (nth j l d)); try intuition.
      - simpl. apply negb_true_iff in H0. unfold elem in H0.
        assert (forall x, In x l -> (if eqDecide a x then true else false) = false)
          by (apply existsb_false; assumption).
        destruct H1.
        destruct H4.
        assert ((i < length l)%nat) by intuition.
        assert (In (nth i l d) l) by (apply nth_In; assumption).
        apply H3 in H7.
        destruct (eqDecide a (nth i l d)); try intuition.
      - destruct H1. destruct H3. simpl in *.
        assert ((i < length l)%nat) by intuition.
        assert ((j < length l)%nat) by intuition.
        assert (i <> j) by intuition.
        assert (distinctIndices i j l) by
            (unfold distinctIndices; split; intuition).
        apply IHl with (i := i) (j := j) (d := d) in H8; intuition.
  * induction l; try reflexivity.
    intros. simpl. apply andb_true_iff. split.
    + apply negb_true_iff. unfold elem.
      apply existsb_false.
      intros.
      destruct (eqDecide a x); try reflexivity.
      assert (exists n, (n < length l)%nat /\ nth n l a = x)
        by (apply In_nth; intuition).
      do 2 (destruct H2).
      assert (nth (S x0) (a :: l) a = x) by intuition.
      assert (nth 0 (a :: l) a = a) by intuition.
      assert (0%nat <> S x0) by intuition.
      assert (S x0 < length (a :: l))%nat by (simpl; intuition).
      assert (distinctIndices 0 (S x0) (a :: l))
        by (unfold distinctIndices; split; intuition).
      apply H0 with (d := a) in H8. simpl in H8.
      rewrite H3 in H8.
      contradiction.
    + apply IHl. intros. unfold distinctIndices in H1.
      destruct H1. destruct H2.
      assert (S i < length (a :: l))%nat by (simpl; intuition).
      assert (S j < length (a :: l))%nat by (simpl; intuition).
      assert (S i <> S j) by intuition.
      assert (distinctIndices (S i) (S j) (a :: l))
        by (unfold distinctIndices; split; intuition).
      apply H0 with (d := d) in H7. simpl in H7. assumption.
Qed.

Corollary distinctComputationFalse {A} `{eqDec A} : forall (l : list A),
    distinct l = false -> ~distinct' l.
Proof.
  intros.
  intro H'.
  apply distinctComputation in H'.
  rewrite H0 in H'. inversion H'.
Qed.

Definition denoteIntTuple (q : Int * Int) : Z * Z :=
  let ' (x, y) := q in (⟦ x ⟧, ⟦ y ⟧).

Lemma distinctIndicesCons {A} : forall (a : A) (l : list A) (i j : nat),
    distinctIndices (S i) (S j) (a :: l) -> distinctIndices i j l.
Proof.
  unfold distinctIndices. simpl. intros.
  destruct H. destruct H0.
  split; intuition.
Qed.

Lemma intBijective : forall (i j : Int),
    ⟦ i ⟧ = ⟦ j ⟧ <-> i = j.
Proof.
  intros. split; intros.  
  * apply denoteInjective. assumption.
  * rewrite H. reflexivity.
Qed.

Lemma distinctBijective {A} {B} : forall (l : list A) (f : A -> B) (a : A),
    (forall (a1 a2 : A), f a1 = f a2 <-> a1 = a2) ->
    distinct' l <-> distinct' (map f l).
Proof.
  intros.
  split; intros.
  * unfold distinct' in *.
    intros.
    assert (length (map f l) = length l) by apply map_length.
    apply distinctIndicesTransfer with (i0 := i) (j0 := j) in H2.
    assert (nth i l a <> nth j l a)
      by (apply H0; apply H2; assumption).
    assert (f (nth i l a) <> f (nth j l a))
      by (intro H'; apply H in H'; contradiction).
    assert (nth i (map f l) (f a) = nth i (map f l) d)
      by (apply nth_indep; destruct H1; intuition).
    assert (nth j (map f l) (f a) = nth j (map f l) d)
      by (apply nth_indep; destruct H1; intuition).
    rewrite <- H5. rewrite <- H6.
    do 2 (rewrite map_nth).
    assumption.
  * unfold distinct' in *.
    intros.
    assert (length (map f l) = length l) by apply map_length.
    apply distinctIndicesTransfer with (i0 := i) (j0 := j) in H2.
    assert (nth i (map f l) (f d) <> nth j (map f l) (f d))
      by (apply H0; apply H2; assumption).
    do 2 (rewrite map_nth in H3).
    intro H'.
    apply H3.
    apply H.
    assumption.
Qed.

Lemma distinctCons {A} : forall (a : A) (l : list A),
    distinct' (a :: l) -> distinct' l.
Proof.
  intros a l. revert a. induction l.
  * unfold distinct'. intros.
    unfold distinctIndices in H0. destruct H0. inversion H0.
  * unfold distinct'. intros.
    unfold distinctIndices in H0.
    destruct H0. destruct H1.
    assert (nth (S i) (a0 :: a :: l) d = nth i (a :: l) d)
      by (simpl; reflexivity).
    assert (nth (S j) (a0 :: a :: l) d = nth j (a :: l) d)
      by (simpl; reflexivity).
    rewrite <- H3. rewrite <- H4.
    apply H.
    unfold distinctIndices.
    split; simpl; intuition.
Qed.

Lemma distinctIntIffDistinctZ : forall (l : list Int),
    distinct' l <-> distinct' (map (fun i => ⟦ i ⟧) l).
Proof.
  intros.
  apply distinctBijective.
  * apply zero.
  * intros. apply intBijective.
Qed.

Lemma fstIntFstZ : forall (l : list (Int * Int)),
    map fst (map denoteIntTuple l) = map (fun i => ⟦ i ⟧) (map fst l).
Proof.
  intros.
  induction l; simpl in *.
  * reflexivity.
  * destruct a. simpl. rewrite <- IHl. reflexivity.
Qed.

Lemma sndIntSndZ : forall (l : list (Int * Int)),
    map snd (map denoteIntTuple l) = map (fun i => ⟦ i ⟧) (map snd l).
Proof.
  intros.
  induction l; simpl in *.
  * reflexivity.
  * destruct a. simpl. rewrite <- IHl. reflexivity.
Qed.

Lemma sumIntSumZ : forall (l : list (Int * Int)),
    map (fun p => fst p + snd p) (map denoteIntTuple l)
    = map (fun i => ⟦ i ⟧) (map (uncurry plus) l).
Proof.
  intros.  
  induction l; simpl in *.
  * reflexivity.
  * destruct a. unfold uncurry in *. simpl.
    rewrite <- rosetteDenotePlusOk. simpl.
    rewrite <- IHl. reflexivity.
Qed.

Lemma diffIntdiffZ : forall (l : list (Int * Int)),
    map (fun p => fst p - snd p) (map denoteIntTuple l)
    = map (fun i => ⟦ i ⟧) (map (uncurry minus) l).
Proof.
  intros.  
  induction l; simpl in *.
  * reflexivity.
  * destruct a. unfold uncurry in *. simpl.
    rewrite <- rosetteDenoteMinusOk. simpl.
    rewrite <- IHl. reflexivity.
Qed.

Theorem isLegalIffNoCollisions : forall (positions : list (Int * Int)),
    isLegal positions = true <->
    noCollisions (map denoteIntTuple positions).
Proof.
  unfold isLegal.
  intros. split; intros.
  * apply noCollisionsIffDistinct.
    assert (forall x, In x
                    [distinct (fst <$> positions);
                     distinct (snd <$> positions);
                     distinct (uncurry plus <$> positions);
                     distinct (uncurry minus <$> positions)]
                 -> x = true)
      by (apply forallb_forall; assumption).
    assert (distinct (fst <$> positions) = true)
      by (apply H0; intuition).
    assert (distinct (snd <$> positions) = true)
      by (apply H0; intuition).
    assert (distinct (uncurry plus <$> positions) = true)
      by (apply H0; intuition).
    assert (distinct (uncurry minus <$> positions) = true)
      by (apply H0; intuition).
    apply distinctComputation in H1.
    apply distinctComputation in H2.
    apply distinctComputation in H3.
    apply distinctComputation in H4.
    rewrite fstIntFstZ.
    rewrite sndIntSndZ.
    rewrite sumIntSumZ.
    rewrite diffIntdiffZ.
    split; [| split; [| split]];
      try (apply distinctIntIffDistinctZ; assumption).
  * apply noCollisionsIffDistinct in H.
    destruct H. destruct H0. destruct H1.
    rewrite fstIntFstZ in H.
    rewrite sndIntSndZ in H0.
    rewrite sumIntSumZ in H1.
    rewrite diffIntdiffZ in H2.
    apply distinctIntIffDistinctZ in H.
    apply distinctIntIffDistinctZ in H0.
    apply distinctIntIffDistinctZ in H1.
    apply distinctIntIffDistinctZ in H2.
    apply distinctComputation in H.
    apply distinctComputation in H0.
    apply distinctComputation in H1.
    apply distinctComputation in H2.
    simpl.
    do 4 (rewrite andb_true_iff).
    split; [| split; [| split; [| split]]]; intuition.
Qed.

Lemma nListSpaceLength {A} : forall (n : nat) (s : Space A) (l : list A),
   Ensembles.In ⟦ nListSpace s n ⟧ l -> length l = n.
Proof.
  intro n.
  induction n; intros.
  * remember (nListSpace s 0) as l'.
    simpl in Heql'.
    rewrite Heql' in H.
    rewrite denoteSymbolicSingleOk in H.
    inversion H.
    reflexivity.
  * remember (nListSpace s (S n)) as l'.
    simpl in Heql'.
    rewrite Heql' in H.
    rewrite denoteSymbolicBindOk in H.
    rewrite bigUnionIsExists in H.
    inversion H.
    destruct H0.
    rewrite denoteSymbolicBindOk in H1.
    rewrite bigUnionIsExists in H1.
    destruct H1.
    destruct H1.
    apply IHn in H0.
    rewrite denoteSymbolicSingleOk in H2.
    inversion H2.
    simpl.
    rewrite H0.
    reflexivity.
Qed.

Lemma denoteNatToInt : forall (n : nat),
    ⟦ natToInt n ⟧ = Z.of_nat n.
Proof.
  intros.
  induction n.
  * simpl. apply rosetteDenoteZeroOk.
  * rewrite Nat2Z.inj_succ.
    assert (Z.succ (Z.of_nat n) = 1 + Z.of_nat n) by omega.
    rewrite H.
    unfold natToInt. unfold natToInt in IHn.
    rewrite denotePlusOk.
    rewrite denoteOneOk.
    rewrite IHn.
    reflexivity.
Qed.    
    
Lemma rangeBounds : forall (n : nat) (i : Int),
    Ensembles.In ⟦ range zero (natToInt n) ⟧ i -> 0 <= ⟦ i ⟧ < Z.of_nat n.
Proof.
  unfold range.
  intros.
  rewrite denoteBindOk in H.
  rewrite bigUnionIsExists in H.
  inversion H.
  destruct H0.
  remember (le zero x && lt x (natToInt n)) as c.
  symmetry in Heqc.
  destruct c.
  - rewrite denoteSymbolicSingleOk in H1.
    inversion H1.
    apply andb_true_iff in Heqc.
    destruct Heqc.
    rewrite denoteLeOk in H3.
    unfold lt in H4.
    apply andb_true_iff in H4.
    destruct H4.
    apply negb_true_iff in H5.
    rewrite denoteLeOk in H4.
    rewrite <- H2.
    rewrite denoteZeroOk in H3.
    rewrite denoteEqualOk in H5.
    assert (natToInt 0 = zero) by intuition.
    rewrite Z.leb_le in H3.
    rewrite Z.leb_le in H4.
    rewrite Z.eqb_neq in H5.
    rewrite denoteNatToInt in H4, H5.
    split; try assumption.
    apply Z_le_lt_eq_dec in H4.
    destruct H4; intuition.
  - rewrite denoteSymbolicEmptyOk in H1.
    inversion H1.
Qed.

Lemma nListSpaceListMember {A} : forall (n : nat) (s : Space A) (l : list A),
    Ensembles.In ⟦ nListSpace s n ⟧ l
    -> forall (a : A), In a l -> Ensembles.In ⟦ s ⟧ a.
Proof.
  intro n. induction n; intros.
  * remember (nListSpace s 0) as l'.
    simpl in Heql'.
    rewrite Heql' in H.
    rewrite denoteSymbolicSingleOk in H.
    simpl in H.
    inversion H.
    rewrite <- H1 in H0.
    inversion H0.
  * remember (nListSpace s (S n)) as l'.
    simpl in Heql'.
    rewrite Heql' in H.
    rewrite denoteSymbolicBindOk in H.
    rewrite bigUnionIsExists in H.
    inversion H.
    destruct H1.
    rewrite denoteSymbolicBindOk in H2.
    rewrite bigUnionIsExists in H2.
    destruct H2. destruct H2.
    rewrite denoteSymbolicSingleOk in H3.
    inversion H3. clear H3.
    rewrite <- H4 in H0.
    inversion H0; subst; intuition.
    apply IHn with (l := x); intuition.
Qed.

Lemma nListSpaceRangeBounds : forall (n : nat) (l : list Int),
    Ensembles.In ⟦ (nListSpace (range zero (natToInt n)) n) ⟧ l
                 -> forall (i : Int), In i l -> 0 <= ⟦ i ⟧ < Z.of_nat n.
Proof.
  intros.
  apply nListSpaceListMember with (a := i) in H; [| assumption].
  apply rangeBounds. assumption.
Qed.  

Lemma indexLength {A} : forall (l : list A), length (index l) = length l.
  intros. unfold index.
  assert (forall (l' : list A) (i : Int),
             length ((fix rec (n : Int) (l0 : list A) {struct l0} : 
                        list (A * Int) :=
                        match l0 with
                        | [] => []
                        | a :: l1 => (a, n) :: rec (plus one n) l1
                        end) i l') = length l').
  * intro l'.
    induction l'; intros; try reflexivity.
    simpl. rewrite IHl'.
    reflexivity.
  * rewrite H. reflexivity.
Qed.    

Lemma indexRecBounds {A} : forall (l' : list A) (i : Int) (p' : A * Int),
    In p'
       ((fix rec (n : Int) (l : list A) {struct l} : 
           list (A * Int) :=
           match l with
           | [] => []
           | a :: l0 => (a, n) :: rec (plus one n) l0
           end) i l')
    -> ⟦ i ⟧ <= ⟦ (snd p') ⟧ < ⟦ i ⟧ + Z.of_nat (length l').
Proof.
  intro l'. induction l'; intros.
  + inversion H.
  + destruct H.
  - replace (⟦ (snd p') ⟧) with (⟦ i ⟧); [| rewrite <- H; intuition].
    simpl.
    rewrite Zpos_P_of_succ_nat.
    omega.
  - apply IHl' in H.
    rewrite rosetteDenotePlusOk in H.
    replace (@one rosetteBasic rosetteInteger) with rosetteOne in H;
      [| reflexivity].
    rewrite rosetteDenoteOneOk in H.
    assert (@denote RosetteInt Z rosetteDenotationInt i =
            @denote (@Int rosetteBasic rosetteInteger) Z
                    rosetteDenotationInt i) by intuition; subst.
    assert (1 + Z.of_nat (length l') = Z.of_nat (length (a :: l')))
      by (replace (Z.of_nat (length (a :: l')))
          with (Z.succ (Z.of_nat (length l')));
          try omega; simpl; rewrite Zpos_P_of_succ_nat; reflexivity).
    rewrite <- H0.
    omega.
Qed.    
     
Lemma indexBounds {A} : forall (l : list A),
    let n := length l in
    forall (p : (A * Int)), In p (index l) -> 0 <= ⟦ snd p ⟧ < Z.of_nat n.
Proof.
  intros. unfold index in H.
  apply (indexRecBounds l zero p) in H.
  replace (@denote (@Int rosetteBasic rosetteInteger) Z
                   rosetteDenotationInt (@zero rosetteBasic rosetteInteger))
  with (@denote RosetteInt Z rosetteDenotationInt rosetteZero) in H;
    [| intuition].
  rewrite rosetteDenoteZeroOk in H.
  replace (Z.of_nat n) with (Z.of_nat (length l)); [| intuition].
  omega.
Qed.

Lemma indexRecPreservesBound : forall (l : list Int) (n : nat),
    (forall (i : Int), In i l -> 0 <= ⟦ i ⟧ < Z.of_nat n)
    -> (forall (p : (Int * Int)) (i : Int), In p
       ((fix rec (n : Int) (l : list Int) {struct l} : 
           list (Int * Int) :=
           match l with
           | [] => []
           | a :: l0 => (a, n) :: rec (plus one n) l0
           end) i l) -> 0 <= ⟦ (fst p) ⟧ < Z.of_nat n).
Proof.
  intro l. induction l; intros.
  * inversion H0.
  * simpl in H0. destruct H0.
    + assert (In a (a :: l)) by intuition.
      apply H in H1.
      rewrite <- H0.
      simpl. simpl in H1.
      assumption.
    + apply IHl with (n := n) in H0; try assumption.
      intros. assert (In i0 (a :: l)) by intuition.
      apply H; assumption.
Qed.      
      
Lemma indexPreservesBound : forall (l : list Int) (n : nat),
    (forall (i : Int), In i l -> 0 <= ⟦ i ⟧ < Z.of_nat n)
    -> (forall (p : (Int * Int)), In p (index l) -> 0 <= ⟦ fst p ⟧ < Z.of_nat n).
Proof.
  intros. unfold index in H0.
  apply indexRecPreservesBound with (n := n) in H0; assumption.
Qed.

Lemma indexAllInBounds : forall (l : list Int),
    let n := length l in
    (forall (i : Int), In i l -> 0 <= ⟦ i ⟧ < Z.of_nat n) ->
    allInBounds (map denoteIntTuple (index l)).
Proof.
  intros. unfold allInBounds. intros.
  apply in_map_iff in H0.
  destruct H0.
  unfold inBounds.
  rewrite map_length. rewrite indexLength.
  destruct H0.
  unfold denoteIntTuple in H0.
  destruct p. destruct x.
  assert (z = ⟦ fst (i, i0) ⟧) by (inversion H0; intuition).
  assert (z0 = ⟦ snd (i, i0) ⟧) by (inversion H0; intuition).
  rewrite H2, H3.
  split.
  * apply indexPreservesBound with (l := l); assumption.
  * apply indexBounds; assumption.
Qed.

Theorem solveNQueensSound : forall (n : nat) (l : list (Int * Int)),
    solveNQueens n = solution l -> correct n (map denoteIntTuple l).
Proof.
  intros.
  unfold correct.
  unfold solveNQueens in H.
  apply searchSolution in H.
  rewrite denoteBindOk in H.
  rewrite bigUnionIsExists in H.
  inversion H.
  destruct H0.
  remember (isLegal (index x)) as legal.
  symmetry in Heqlegal.
  destruct legal.
  * rewrite denoteSymbolicSingleOk in H1.
    inversion H1.
    apply isLegalIffNoCollisions in Heqlegal.
    split; [| split].
    - rewrite map_length. rewrite indexLength.
      apply nListSpaceLength in H0. assumption.
    - inversion H1.
      apply indexAllInBounds.
      apply nListSpaceRangeBounds.
      assert (length x = n)
        by (apply nListSpaceLength with (s := range zero (natToInt n));
            assumption).
      rewrite H4.
      assumption.
    - assumption.
  * rewrite denoteEmptyOk in H1.
    inversion H1.
Qed.

Lemma distinctPermutation {A} : forall (l1 l2 : list A),
    Permutation l1 l2 -> distinct' l1 -> distinct' l2.
Proof.
  unfold distinct'. intros.
  apply Permutation_nth with (d := d) in H.
  destruct H.
  destruct H2 as [f H2].
  destruct H2.
  destruct H3.
  symmetry in H.
  assert (distinctIndices i j l1)
    by (apply distinctIndicesTransfer with (i0 := i) (j0 := j) in H;
        intuition).  
  unfold distinctIndices in H1, H5.
  destruct H1.
  destruct H6.
  destruct H5.
  destruct H8.
  assert (nth i l2 d = nth (f i) l1 d) by (apply H4; assumption).
  assert (nth j l2 d = nth (f j) l1 d) by (apply H4; assumption).
  assert (distinctIndices (f i) (f j) l1) by (split; intuition).
  apply H0 with (d := d) in H12.
  rewrite H10. rewrite H11.
  assumption.
Qed.

Lemma permutationNoCollisions : forall (l1 l2 : list (Z*Z)),
    Permutation l1 l2 -> noCollisions l1 -> noCollisions l2.
Proof.
  intros.
  apply noCollisionsIffDistinct in H0.
  destruct H0. destruct H1. destruct H2.
  assert (Permutation (map fst l1) (map fst l2))
    by (apply Permutation_map; assumption).
  assert (Permutation (map snd l1) (map snd l2))
    by (apply Permutation_map; assumption).
  assert (Permutation (map (fun p => fst p + snd p) l1)
                      (map (fun p => fst p + snd p) l2))
    by (apply Permutation_map; assumption).
  assert (Permutation (map (fun p => fst p - snd p) l1)
                      (map (fun p => fst p - snd p) l2))
    by (apply Permutation_map; assumption).
  apply noCollisionsIffDistinct.
  split; [| split; [| split]].
  * apply distinctPermutation with (map fst l1); intuition.
  * apply distinctPermutation with (map snd l1); intuition.
  * apply distinctPermutation with (map (fun p => fst p + snd p) l1); intuition.
  * apply distinctPermutation with (map (fun p => fst p - snd p) l1); intuition.
Qed.    

Lemma permutationIsLegal : forall (l1 l2 : list (Int * Int)),
    Permutation l1 l2 -> isLegal l1 = true -> isLegal l2 = true.
Proof.
  intros.
  apply isLegalIffNoCollisions.
  apply isLegalIffNoCollisions in H0.
  assert (Permutation (map denoteIntTuple l1) (map denoteIntTuple l2))
    by (apply Permutation_map; intuition).
  apply permutationNoCollisions with (map denoteIntTuple l1); intuition.
Qed.

Lemma permutationCorrect : forall (l1 l2 : list (Int*Int)) (n : nat),
    Permutation l1 l2
    -> correct n (map denoteIntTuple l1) -> correct n (map denoteIntTuple l2).
Proof.
  unfold correct. unfold allInBounds.
  intros.
  destruct H0.
  destruct H1.
  assert (Permutation (map denoteIntTuple l1) (map denoteIntTuple l2))
    by (apply Permutation_map; assumption).
  assert (length (map denoteIntTuple l1) = length (map denoteIntTuple l2))
    by (apply Permutation_length; assumption).
  split; [| split].
  * intuition.
  * intros.
    rewrite <- H4.
    apply H1.
    apply Permutation_in with (l := map denoteIntTuple l2); try assumption.
    apply Permutation_sym. assumption.
  * apply permutationNoCollisions with (l1 := map denoteIntTuple l1);
      assumption.
Qed.    

Lemma permutationCorrect' : forall (l1 l2 : list (Z*Z)) (n : nat),
    Permutation l1 l2 -> correct n l1 -> correct n l2.
Proof.
  unfold correct. unfold allInBounds.
  intros.
  destruct H0. destruct H1.
  assert (length l1 = length l2) by (apply Permutation_length; assumption).
  rewrite H3 in H0.
  split; try assumption.
  apply permutationNoCollisions with (l2 := l2) in H2; [| assumption].
  split; try assumption.
  rewrite <- H3.
  intros.
  apply Permutation_in with (l' := l1) in H4;
    [| apply Permutation_sym; assumption].
  apply H1; assumption.
Qed.

Definition zToInt (z : Z) : Int. Admitted.

Lemma zToIntOk : forall (z : Z), ⟦ zToInt z ⟧ = z. Admitted.

Lemma zToIntZeroOk : zToInt 0 = zero.
  apply denoteInjective.
  rewrite denoteZeroOk.
  apply zToIntOk.
Qed.

Lemma zToIntOneOk : zToInt 1 = one.
  apply denoteInjective.
  rewrite denoteOneOk.
  apply zToIntOk.
Qed.

Lemma zToIntPlusOk : forall (i j : Z), zToInt (i + j) = plus (zToInt i) (zToInt j).
  intros.
  apply denoteInjective.
  rewrite denotePlusOk.
  do 3 (rewrite zToIntOk).
  reflexivity.
Qed.

Lemma zToIntEqualOk : forall (i j : Z),
    equal (zToInt i) (zToInt j) = Z.eqb i j.
Proof.
  intros.
  rewrite denoteEqualOk.
  do 2 (rewrite zToIntOk).
  reflexivity.
Qed.

Lemma zToIntLeOk : forall (i j : Z),
    le (zToInt i) (zToInt j) = Z.leb i j.
Proof.
  intros.
  rewrite denoteLeOk.
  do 2 (rewrite zToIntOk).
  reflexivity.
Qed.

Definition zTupleToIntTuple (p : Z*Z) : (Int*Int) :=
  let '(x, y) := p in (zToInt x, zToInt y).

Module Import ZOrder := OTF_to_TTLB Z.
Module Import ZSort := Sort ZOrder.

Module ZZOrder <: TotalLeBool.
  Definition t : Set := (Z*Z).
  Definition leb (x y : t) : bool := ZOrder.leb (snd x) (snd y).
  Theorem leb_total : forall (x y : t), leb x y = true \/ leb y x = true.
    intros. destruct x. destruct y.
    unfold leb. simpl.
    apply ZOrder.leb_total.
  Qed.
End ZZOrder.
Module Import ZZSort := Sort ZZOrder.

Lemma indexPreservesFst {A} : forall (l : list A), (map fst (index l)) = l.
  unfold index.
  assert (forall l' i,
             map fst 
                 ((fix rec (n : Int) (l0 : list A) {struct l0} :=
                    match l0 with
                    | [] => []
                    | a :: l1 => (a, n) :: rec (plus one n) l1
                    end) i l') = l').
  * intro l'. induction l'; intros; try intuition.
    simpl. rewrite IHl'. reflexivity.
  * intros. rewrite H. reflexivity.
Qed.

Fixpoint countUp (n : nat) (start : Int) : list Int :=
  match n with
  | S n' => start :: countUp n' (plus one start)
  | O => []
  end.

Lemma sndIndexCountsUp {A} : forall (l : list A) (n : nat),
    length l = n -> map snd (index l) = countUp n zero.
Proof.
  unfold index.
  assert (forall (l' : list A) (n' : nat) (i : Int),
             length l' = n' ->
             map snd ((fix rec (n0 : Int) (l0 : list A) {struct l0} :=
                         match l0 with
                         | [] => []
                         | a :: l1 => (a, n0) :: rec (plus one n0) l1
                         end) i l') = countUp n' i).
  * intro l'. induction l'; intros.
    + simpl in H. subst. reflexivity.
    + simpl. simpl in H. destruct n'; inversion H.
      rewrite IHl' with (n' := n'); [| assumption].
      rewrite H1. intuition.
  * intros. rewrite H with (n' := n); [| assumption].
    reflexivity.
Qed.
      
Lemma sndIndex {A} : forall (l : list (A*Int)) (n : nat),
    length l = n -> map snd l = countUp n zero -> index (map fst l) = l.
Proof.
  unfold index.
  assert (forall (l' : list (A * Int)) (n' : nat) (i : Int),
             length l' = n' ->
             map snd l' = countUp n' i ->
             (fix rec (n0 : Int) (l0 : list A) {struct l0} :=
                match l0 with
                | [] => []
                | a :: l1 => (a, n0) :: rec (plus one n0) l1
                end) i (map fst l') = l').
  * intro l'. induction l'; intros; try reflexivity.
    destruct n'; inversion H.
    simpl in H0. inversion H0.
    simpl. rewrite IHl' with (n' := n'); try assumption.
    destruct a; reflexivity.
  * intros. rewrite H with (n' := n); intuition.
Qed.    

Lemma intToZInvolutive : forall (p : Z*Z),
    denoteIntTuple (zTupleToIntTuple p) = p.
Proof.
  intros. destruct p. simpl.
  do 2 (rewrite zToIntOk).
  reflexivity.
Qed.

Lemma intToZInvolutiveMap : forall (l : list (Z*Z)),
    map denoteIntTuple (map zTupleToIntTuple l) = l.
Proof.
  intros.
  induction l.
  * reflexivity.
  * simpl. rewrite intToZInvolutive.
    simpl in IHl. rewrite IHl.
    reflexivity.
Qed.

Lemma intSndToZSnd : forall (l : list (Z*Z)),
    map snd (map zTupleToIntTuple l) = map zToInt (map snd l).
Proof.
  intros.
  induction l; try reflexivity.
  simpl. simpl in IHl. rewrite IHl.
  destruct a. simpl. reflexivity.
Qed.

Lemma zToIntInj : forall (z1 z2 : Z),
    zToInt z1 = zToInt z2 -> z1 = z2.
Proof.
  intros.
  rewrite <- (zToIntOk z1).
  rewrite <- (zToIntOk z2).
  rewrite H. reflexivity.
Qed.

Lemma zToIntMapInj : forall (l1 l2 : list Z),
    map zToInt l1 = map zToInt l2 -> l1 = l2.
Proof.
  intro l1. induction l1; intros.
  * simpl in H. destruct l2; try inversion H. reflexivity.
  * simpl in H. destruct l2; try inversion H.
    apply IHl1 in H2. apply zToIntInj in H1. subst.
    reflexivity.
Qed.

Lemma zToIntMapBij : forall (l1 l2 : list Z),
    map zToInt l1 = map zToInt l2 <-> l1 = l2.
Proof.
  intros. split; intros.
  * apply zToIntMapInj; assumption.
  * rewrite H. reflexivity.
Qed.

Lemma zToIntInv : forall (i : Int), zToInt ⟦ i ⟧ = i.
  intros.
  apply denoteInjective.
  rewrite zToIntOk.
  reflexivity.
Qed.  

Fixpoint zCountUp (n : nat) (start : Z) : list Z :=
  match n with
  | S n' => start :: zCountUp n' (1 + start)
  | O => []
  end.

Lemma countUpToZCountUp : forall (n : nat) (start : Int),
    countUp n start = map zToInt (zCountUp n ⟦ start ⟧).
Proof.
  intro n. induction n; intros.
  * reflexivity.
  * unfold countUp. rewrite IHn. unfold zCountUp.
    rewrite rosetteDenotePlusOk.
    replace (@denote RosetteInt Z rosetteDenotationInt
                     (@one rosetteBasic rosetteInteger))
    with (@denote RosetteInt Z rosetteDenotationInt rosetteOne);
      [| intuition].
    rewrite rosetteDenoteOneOk. simpl.
    rewrite zToIntInv.
    reflexivity.
Qed.

Lemma sortedBySecond : forall (l : list (Z*Z)),
    Sorted.LocallySorted (fun p1 p2 => is_true (leb (snd p1) (snd p2))) l
    -> Sorted.LocallySorted (fun z1 z2 => is_true (leb z1 z2)) (map snd l).
Proof.
  intros; induction H; simpl; constructor; try assumption.
Qed.

Lemma ZofSucc : forall (n : nat), Z.of_nat (S n) = 1 + Z.of_nat n.
  intros. induction n.
  * simpl. reflexivity.
  * unfold Z.of_nat. do 2 (rewrite Zpos_P_of_succ_nat).
    rewrite IHn. omega.
Qed.

Lemma sortedListAllGreater : forall (l : list Z) (a : Z),
    Sorted.Sorted (fun z1 z2 => is_true (leb z1 z2)) l
    -> Sorted.HdRel (fun z1 z2 : Z => is_true (leb z1 z2)) a l
    -> (forall z, In z l -> a <= z).
Proof.
  intros l a H. revert a. induction H; intros.
  * inversion H0.
  * assert (forall z, In z l -> a <= z) by (apply IHSorted; assumption).
    apply Sorted.HdRel_inv in H1.
    apply leb_le in H1.
    apply Z.compare_ngt_iff in H1.
    assert (a0 <= a) by omega.
    destruct H2; try omega.
    apply H3 in H2. omega.
Qed.    
    
Theorem sortDistinctListRangeGeneral : forall (l : list Z) (n : nat) (i : Z),
    Sorted.LocallySorted (fun z1 z2 => is_true (leb z1 z2)) l
    -> length l = n
    -> distinct' l -> (forall z, In z l -> i <= z < i + Z.of_nat n)
    -> l = zCountUp n i.
Proof.
  intros l n i H. revert n i.
  induction H; intros.
  * simpl in H. rewrite <- H. reflexivity.
  * simpl in H. rewrite <- H. simpl.
    rewrite <- H in H1. simpl in H1.
    assert (i <= a < i + 1) by (apply H1; intuition).
    assert (a = i) by omega.
    rewrite H3. reflexivity.
  * assert (distinct' (b :: l))
      by (apply distinctCons with (a0 := a); assumption).
    destruct n; inversion H1.
    destruct n; inversion H6.
    assert (length (b :: l) = S n) by intuition.
    assert (a <= b)
      by (apply leb_le in H0; apply Z.compare_ngt_iff in H0; omega).
    assert (i <= a) by (apply H3; intuition).
    apply Sorted.Sorted_LocallySorted_iff in H.
    assert (Sorted.HdRel (fun z1 z2 : Z => is_true (leb z1 z2)) a (b :: l))
      by (apply Sorted.HdRel_cons; assumption).
    assert (a <> b) by
        (unfold distinct' in H2;
         assert (distinctIndices 0 1 (a :: b :: l)) by (split; omega);
         apply H2 with (d := 0) in H11;
         simpl in H11;
         assumption).
    apply Z.le_lteq in H8.
    destruct H8; try contradiction.
    assert (i + 1 <= b) by omega.
    assert (is_true (leb (i + 1) b))
      by (apply leb_le; apply Z.compare_ngt_iff; omega).
    apply Sorted.HdRel_cons with (a := i + 1) (b := b) (l := l) in H13.
    assert (forall z, In z (b :: l) -> i + 1 <= z)
      by (apply sortedListAllGreater; assumption).
    assert (forall z, In z (b :: l) -> i + 1 <= z < i + 1 + Z.of_nat (S n))
      by (intros; split; try (intuition; omega);
          assert (In z (a :: b :: l)) by intuition;
          apply H3 in H16; rewrite ZofSucc in H16; omega).
    assert (b :: l = zCountUp (S n) (i + 1))
           by (apply IHLocallySorted; assumption).
    rewrite H6.
    assert (zCountUp (S (S n)) i = i :: zCountUp (S n) (i + 1))
      by (assert (i + 1 = 1 + i) by omega; rewrite H17; intuition).
    rewrite H17. rewrite <- H16.
    assert (b = i + 1) by (inversion H16; intuition).
    assert (a = i) by omega.
    rewrite H19.
    reflexivity.
Qed.    
    
Lemma sortDistinctListRange : forall (l : list Z) (n : nat),
    length l = n
    -> distinct' l -> (forall z, In z l -> 0 <= z < Z.of_nat n)
    -> Sorted.LocallySorted (fun z1 z2 => is_true (leb z1 z2)) l
    -> l = zCountUp n 0.
Proof.
  intros. apply sortDistinctListRangeGeneral; assumption.
Qed.
      
Lemma sortedIndex : forall (p : list (Z*Z)) (n : nat),
    correct n p ->
    map zTupleToIntTuple (sort p)
    = index (map fst (map zTupleToIntTuple (sort p))).
Proof.
  intros.
  assert (Permutation p (sort p)) by (apply Permuted_sort).
  destruct H. destruct H1.
  apply noCollisionsIffDistinct in H2.
  unfold allInBounds in H1. unfold inBounds in H1.
  rewrite sndIndex with (n0 := n).
  * reflexivity.
  * rewrite map_length. rewrite <- H.
    apply Permutation_length. apply Permutation_sym.
    assumption.
  * rewrite intSndToZSnd. rewrite countUpToZCountUp. rewrite zToIntMapBij.
    replace (@denote (@Int rosetteBasic rosetteInteger) Z rosetteDenotationInt
                     (@zero rosetteBasic rosetteInteger))
    with (@denote RosetteInt Z rosetteDenotationInt rosetteZero);
      [| intuition].
    rewrite rosetteDenoteZeroOk.
    destruct H2. destruct H3.
    assert (Sorted.LocallySorted
              (fun p1 p2 => is_true (leb (snd p1) (snd p2))) (sort p))
      by apply Sorted_sort.
    apply sortedBySecond in H5.
    assert (Permutation (map snd p) (map snd (sort p)))
      by (apply Permutation_map; assumption).
    assert (distinct' (map snd (sort p)))
      by (apply distinctPermutation with (l1 := map snd p); assumption).
    assert (length (map snd (sort p)) = n)    
      by (rewrite <- H; rewrite map_length; apply Permutation_length;
          apply Permutation_sym; intuition).
    apply sortDistinctListRange; try assumption.
    intros. apply in_map_iff in H9. do 2 (destruct H9).
    apply Permutation_in with (l' := p) in H10;
      [| apply Permutation_sym; assumption].
    apply H1 in H10.
    destruct x. simpl in H9. rewrite <- H9. 
    intuition.
Qed.

Lemma inRangeIfInBounds : forall (z : Z) (n : nat),
    0 <= z < Z.of_nat n -> Ensembles.In ⟦ range zero (natToInt n) ⟧ (zToInt z).
Proof.
  intros.
  unfold range.
  rewrite denoteBindOk.
  rewrite bigUnionIsExists.
  exists (zToInt z).
  split.
  * rewrite denoteFullOk. constructor.
  * unfold lt.
    do 2 (rewrite denoteLeOk). rewrite denoteZeroOk.
    rewrite denoteEqualOk.
    rewrite zToIntOk.
    rewrite denoteNatToInt.    
    assert ((0 <=? z) && ((z <=? Z.of_nat n)
                            && negb (Z.eqb z (Z.of_nat n))) = true).
    apply andb_true_iff.
    split; [| apply andb_true_iff; split].
    + destruct H. apply Z.leb_le. assumption.
    + apply Z.leb_le. omega.
    + apply negb_true_iff. apply Z.eqb_neq. omega.
    + rewrite H0. rewrite denoteSymbolicSingleOk.
      constructor.
Qed.

Lemma lengthZeroMeansEmpty {A} : forall (l : list A),
    length l = 0%nat -> l = [].
Proof.
  intros.
  destruct l.
  * reflexivity.
  * inversion H.
Qed.

Lemma inNListSpaceIfInSpace {A} : forall (l : list A) (s : Space A) (n : nat),
    length l = n ->
    (forall a, In a l -> Ensembles.In ⟦ s ⟧ a) -> Ensembles.In ⟦ nListSpace s n ⟧ l.
Proof.
  intro l. induction l; intros.
  * simpl in H. rewrite <- H.
    unfold nListSpace. rewrite denoteSymbolicSingleOk.
    simpl. constructor.
  * simpl in H.
    destruct n; inversion H.
    unfold nListSpace.
    rewrite denoteSymbolicBindOk.
    rewrite bigUnionIsExists.
    assert (forall a0 : A, In a0 l -> Ensembles.In ⟦ s ⟧ a0)
      by (intros; apply H0; simpl; right; assumption).
    exists l.
    split.
    + apply IHl; intuition.
    + rewrite denoteSymbolicBindOk.
      rewrite bigUnionIsExists.
      exists a.
      split.
      - apply H0. intuition.
      - rewrite denoteSymbolicSingleOk.
        constructor.
Qed.

Lemma correctArrangementsInIndex : forall (p : list (Z*Z)) (n : nat),
    correct n p ->
    (exists p', Permutation p p'
           /\ Ensembles.In ⟦ bind (nListSpace (range zero (natToInt n)) n)
                                 (fun xs:list Int => if isLegal (index xs)
                                                  then single (index xs)
                                                  else empty) ⟧
                          (map zTupleToIntTuple p')).
Proof.
  intros.
  exists (ZZSort.sort p).
  assert (Permutation p (sort p)) by apply Permuted_sort.
  split; try assumption.
  rewrite denoteSymbolicBindOk.
  rewrite bigUnionIsExists.
  assert (correct n (sort p))
    by (apply permutationCorrect' with (l1 := p); assumption).
  exists (map fst (map zTupleToIntTuple (sort p))).
  split.
  * unfold correct in H1.
    destruct H1.
    destruct H2.
    unfold allInBounds in H2. unfold inBounds in H2.
    apply inNListSpaceIfInSpace; try (do 2 (rewrite map_length); assumption).
    intros.
    apply in_map_iff in H4.
    do 2 (destruct H4).
    apply in_map_iff in H5.
    do 2 (destruct H5).
    destruct x. destruct x0.
    simpl in H5.
    rewrite <- H4.
    inversion H5; subst.
    apply inRangeIfInBounds.
    apply H2 in H6. destruct H6.
    assumption.
  * assert (index (map fst (map zTupleToIntTuple (sort p))) =
            map zTupleToIntTuple (sort p))
      by (symmetry; apply sortedIndex with (n := n); assumption).
    rewrite H2.
    assert (isLegal (map zTupleToIntTuple (sort p)) = true)
      by (apply isLegalIffNoCollisions;
          rewrite intToZInvolutiveMap;
          unfold correct in H1;
          destruct H1; destruct H3;
          assumption).
    rewrite H3.
    rewrite denoteSymbolicSingleOk.
    constructor.
Qed.
  
Theorem solveNQueensComplete : forall (n : nat),
    solveNQueens n = uninhabited -> ~exists l, correct n l.
Proof.
  intros.
  intro H'.
  destruct H'.
  apply correctArrangementsInIndex in H0.
  do 2 (destruct H0).
  unfold solveNQueens in H.
  apply searchUninhabited in H.
  simpl in *.
  rewrite H in H1.
  inversion H1.
Qed.
