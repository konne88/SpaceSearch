Require Import Basic.
Require Import Heuristic.
Require Import Full.
Require Import ListEx.
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
Require Import Psatz. (* for lia *)
Require Import Space.Tactics.

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

Section Queens.
Context `{BAS:Basic}.
Context `{SEA:@Search BAS}.
Context `{INT:@Integer BAS}.

Definition uncurry {A B C} (f:A->B->C) (ab:A*B) : C :=
  f (fst ab) (snd ab).

Fixpoint nListSpace `{Basic} {A} (s:Space A) (n:nat) : Space (list A) :=
  match n with
  | 0%nat => single []
  | S n => bind (nListSpace s n) (fun l =>
          bind s (fun a => single (a :: l)))
  end.

Fixpoint index' {A} n (l : list A) :=
  match l with
  | [] => []
  | a::l => (a,n) :: index' (plus one n) l
  end.

Definition index {A} : list A -> list (A * Int) :=
  index' zero.

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
  intros. lia.
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
  lia.
Qed.

Definition noCollisions' (positions : list (Z*Z)) : Prop :=
  ~exists (i j : nat), distinctIndices i j positions
                /\ collision (ith i positions) (ith j positions).

Lemma collisionsEquiv : forall (positions : list (Z*Z)),
    noCollisions positions <-> noCollisions' positions.
Proof.
  firstorder idtac.
Qed.

Definition existsCollision (positions : list (Z*Z)) : Prop :=
  exists (i j : nat), distinctIndices i j positions
               /\ collision (ith i positions) (ith j positions).

Lemma existsCollisionNot : forall (positions : list (Z*Z)),
    existsCollision positions <-> ~noCollisions positions.
Proof.
  intros. unfold existsCollision. unfold noCollisions.
  firstorder idtac.
  apply not_all_ex_not in H. destruct H.
  apply not_all_ex_not in H. destruct H.
  apply imply_to_and in H. destruct H.
  apply NNPP in H0.
  firstorder idtac.
Qed.

Definition forSomePairAlike (positions : list (Z*Z))
           (quantity : (Z*Z) -> Z) : Prop :=
  exists (i j: nat), distinctIndices i j positions
              /\ quantity (ith i positions) = quantity (ith j positions).

Lemma xAlikeCollision : forall (positions : list (Z*Z)),
    forSomePairAlike positions (fun p => fst p)
    -> existsCollision positions.
Proof.
  unfold existsCollision, forSomePairAlike.
  intros.
  destruct H as (i & j & D & E).
  exists i, j.
  unfold collision.
  repeat break_match.
  intuition.
Qed.

Lemma yAlikeCollision : forall (positions : list (Z*Z)),
    forSomePairAlike positions (fun p => snd p)
    -> existsCollision positions.
Proof.
  unfold existsCollision, forSomePairAlike.
  intros.
  destruct H as (i & j & D & E).
  exists i, j.
  unfold collision.
  repeat break_match.
  intuition.
Qed.

Lemma sumAlikeCollision : forall (positions : list (Z*Z)),
    forSomePairAlike positions (fun p => fst p + snd p)
    -> existsCollision positions.
Proof.
  unfold existsCollision, forSomePairAlike.
  intros.
  destruct H as (i & j & D & E).
  exists i, j.
  unfold collision.
  repeat break_match.
  split; auto.
  right. right.
  apply diagonalOptimization.
  auto.
Qed.

Lemma diffAlikeCollision : forall (positions : list (Z*Z)),
    forSomePairAlike positions (fun p => fst p - snd p)
    -> existsCollision positions.
Proof.
  unfold existsCollision, forSomePairAlike.
  intros.
  destruct H as (i & j & D & E).
  exists i, j.
  unfold collision.
  repeat break_match.
  split; auto.
  right. right.
  apply diagonalOptimization.
  auto.
Qed.

Lemma alikeIfCollision : forall (positions : list (Z*Z)),
    existsCollision positions ->
    forSomePairAlike positions (fun p => fst p)
    \/ forSomePairAlike positions (fun p => snd p)
    \/ forSomePairAlike positions (fun p => fst p + snd p)
    \/ forSomePairAlike positions (fun p => fst p - snd p).
Proof.
  unfold existsCollision, forSomePairAlike, collision.
  intros ? (i & j & D & C).
  repeat break_match.
  (intuition idtac); [left|
                      right; left|
                      right; right; apply diagonalOptimization in H0;
                        destruct H0; [left | right]];
  (exists i, j; rewrite Heqp; rewrite Heqp0; intuition).
Qed.

Theorem collisionIffAlike : forall (positions : list (Z*Z)),
    existsCollision positions <->
    forSomePairAlike positions (fun p => fst p)
    \/ forSomePairAlike positions (fun p => snd p)
    \/ forSomePairAlike positions (fun p => fst p + snd p)
    \/ forSomePairAlike positions (fun p => fst p - snd p).
Proof.
  intros. split; intros.
  * auto using alikeIfCollision.
  * destruct H as [|[|[|]]].
    - auto using xAlikeCollision.
    - auto using yAlikeCollision.
    - auto using sumAlikeCollision.
    - auto using diffAlikeCollision.
Qed.

Definition distinct' {A} (l : list A) : Prop :=
  forall (i j : nat) (d : A), distinctIndices i j l -> nth i l d <> nth j l d.

Lemma distinct'_iff_NoDup : forall A (l : list A), distinct' l <-> NoDup l.
Proof.
  unfold distinct'.
  destruct l.
  - intuition. constructor. destruct H0. simpl in *. omega.
  - split; intros.
    + rewrite NoDup_nth with (d := a).
      revert H. generalize (a :: l). clear l. intros.
      destruct (eq_nat_dec i j); firstorder idtac.
    + revert H H0. generalize (a :: l). clear l. intros.
      rewrite NoDup_nth with (d := d) in H.
      firstorder.
Qed.

Lemma distinctIndicesTransfer {A B} :
  forall (l1 : list A) (l2 : list B) (i j : nat),
    length l1 = length l2 ->
    distinctIndices i j l1 -> distinctIndices i j l2.
Proof. unfold distinctIndices. intuition. Qed.

Lemma notAlikeIffDistinct :
  forall (positions : list (Z*Z)) (quantity : (Z*Z) -> Z),
    distinct' (map quantity positions)
    <-> ~forSomePairAlike positions quantity.
Proof.
  intros. unfold forSomePairAlike, distinct'.
  split; intros.
  * intro H'. destruct H' as (i & j & D & Q).
    unfold ith in Q.
    rewrite <- !map_nth with (f := quantity) in Q.
    eapply H; eauto.
    eapply distinctIndicesTransfer; [|eauto].
    auto using map_length.
  * intro H'.
    apply H.
    exists i, j.
    split.
    + eapply distinctIndicesTransfer; eauto using map_length.
    + unfold ith.
      rewrite <- !map_nth with (f := quantity).
      rewrite !nth_indep with (d := quantity _) (d' := d) by firstorder.
      assumption.
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
  * destruct H as (Hx & Hy & Hs & Hd).
    apply collisionsEquiv. unfold noCollisions'. intro H.
    apply notAlikeIffDistinct in Hx.
    apply notAlikeIffDistinct in Hy.
    apply notAlikeIffDistinct in Hs.
    apply notAlikeIffDistinct in Hd.
    destruct H as (i & j & D & Q).
    unfold collision in Q. unfold forSomePairAlike in *.
    remember (ith i positions) as p1.
    remember (ith j positions) as p2.
    destruct p1 as [x1 y1]. destruct p2 as [x2 y2].
    destruct Q; [apply Hx |
      destruct H; [apply Hy |
        apply diagonalOptimization in H;
        destruct H; [apply Hs | apply Hd]]];
    (exists i; exists j; rewrite <- Heqp1; rewrite <- Heqp2; split; intuition).
Qed.

Theorem distinctComputation {A} `{eqDec A} : forall (l : list A),
    distinct l = true <-> distinct' l.
Proof.
  intros l.
  rewrite distinct_iff_NoDup, distinct'_iff_NoDup.
  intuition.
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
  rewrite !distinct'_iff_NoDup.
  split; intros.
  * apply FinFun.Injective_map_NoDup; firstorder.
  * eauto using NoDup_map_inv.
Qed.

Lemma distinctCons {A} : forall (a : A) (l : list A),
    distinct' (a :: l) -> distinct' l.
Proof.
  intros a l.
  rewrite !distinct'_iff_NoDup.
  now inversion 1.
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
  rewrite !map_map.
  apply map_ext.
  destruct a.
  reflexivity.
Qed.

Lemma sndIntSndZ : forall (l : list (Int * Int)),
    map snd (map denoteIntTuple l) = map (fun i => ⟦ i ⟧) (map snd l).
Proof.
  intros.
  rewrite !map_map.
  apply map_ext.
  destruct a.
  reflexivity.
Qed.

Lemma sumIntSumZ : forall (l : list (Int * Int)),
    map (fun p => fst p + snd p) (map denoteIntTuple l)
    = map (fun i => ⟦ i ⟧) (map (uncurry plus) l).
Proof.
  intros.
  rewrite !map_map.
  apply map_ext.
  destruct a.
  unfold uncurry.
  space_crush.
Qed.

Lemma diffIntdiffZ : forall (l : list (Int * Int)),
    map (fun p => fst p - snd p) (map denoteIntTuple l)
    = map (fun i => ⟦ i ⟧) (map (uncurry minus) l).
Proof.
  intros.
  rewrite !map_map.
  apply map_ext.
  destruct a.
  unfold uncurry.
  space_crush.
Qed.

Theorem isLegalIffNoCollisions : forall (positions : list (Int * Int)),
    isLegal positions = true <->
    noCollisions (map denoteIntTuple positions).
Proof.
  unfold isLegal.
  intros. split; intros.
  * rewrite forallb_forall in H.
    rewrite noCollisionsIffDistinct.
    rewrite fstIntFstZ.
    rewrite sndIntSndZ.
    rewrite sumIntSumZ.
    rewrite diffIntdiffZ.
    rewrite <- !distinctIntIffDistinctZ.
    rewrite <- !@distinctComputation.
    intuition.
  * apply noCollisionsIffDistinct in H.
    destruct H as (R & C & D1 & D2).
    rewrite fstIntFstZ in *.
    rewrite sndIntSndZ in *.
    rewrite sumIntSumZ in *.
    rewrite diffIntdiffZ in *.
    rewrite <- distinctIntIffDistinctZ in *.
    rewrite <- !@distinctComputation with (H := eqDecInteger) in *.
    rewrite forallb_forall. intro x.
    simpl.
    intuition congruence.
Qed.

Lemma nListSpaceLength {A} : forall (n : nat) (s : Space A) (l : list A),
   Ensembles.In ⟦ nListSpace s n ⟧ l -> length l = n.
Proof.
  intro n.
  induction n; simpl; intros; space_crush.
  subst. simpl. eauto.
Qed.

Lemma denoteNatToInt : forall (n : nat),
    ⟦ natToInt n ⟧ = Z.of_nat n.
Proof.
  intros.
  induction n; cbn [natToInt]; space_crush.
  lia.
Qed.
Hint Rewrite denoteNatToInt : space.

Lemma rangeBounds : forall (n : nat) (i : Int),
    Ensembles.In ⟦ range zero (natToInt n) ⟧ i -> 0 <= ⟦ i ⟧ < Z.of_nat n.
Proof.
  unfold range.
  intros.
  space_crush.
  break_if; space_crush.
Qed.

Lemma nListSpaceListMember {A} : forall (n : nat) (s : Space A) (l : list A),
    Ensembles.In ⟦ nListSpace s n ⟧ l
    -> forall (a : A), In a l -> Ensembles.In ⟦ s ⟧ a.
Proof.
  induction n; simpl; intros; space_crush; simpl in *; intuition idtac; eauto; congruence.
Qed.

Lemma nListSpaceRangeBounds : forall (n : nat) (l : list Int),
    Ensembles.In ⟦ (nListSpace (range zero (natToInt n)) n) ⟧ l
                 -> forall (i : Int), In i l -> 0 <= ⟦ i ⟧ < Z.of_nat n.
Proof.
  intros.
  apply nListSpaceListMember with (a := i) in H; [| assumption].
  apply rangeBounds. assumption.
Qed.

Lemma indexLength' {A} : forall (l : list A) (i : Int),
    length (index' i l) = length l.
Proof.
  induction l; simpl; auto.
Qed.

Lemma indexLength {A} : forall (l : list A), length (index l) = length l.
  intros.
  apply indexLength'.
Qed.
Hint Rewrite @indexLength : list.

Lemma indexBounds' {A} : forall (l' : list A) (i : Int) (p' : A * Int),
    In p' (index' i l')
    -> ⟦ i ⟧ <= ⟦ (snd p') ⟧ < ⟦ i ⟧ + Z.of_nat (length l').
Proof.
  induction l'; simpl; intros.
  - intuition.
  - destruct H.
    + subst. simpl. lia.
    + apply IHl' in H.
      space_crush. lia.
Qed.

Lemma indexBounds {A} : forall (l : list A),
    let n := length l in
    forall (p : (A * Int)), In p (index l) -> 0 <= ⟦ snd p ⟧ < Z.of_nat n.
Proof.
  unfold index.
  intros.
  apply (indexBounds' l zero p) in H.
  space_crush.
Qed.

Lemma indexPreservesBound' : forall (l : list Int) (n : nat),
    (forall (i : Int), In i l -> 0 <= ⟦ i ⟧ < Z.of_nat n)
    -> (forall (p : (Int * Int)) (i : Int), In p
       (index' i l) -> 0 <= ⟦ (fst p) ⟧ < Z.of_nat n).
Proof.
  induction l; simpl; intros.
  - intuition.
  - destruct H0; subst; eauto.
Qed.

Lemma indexPreservesBound : forall (l : list Int) (n : nat),
    (forall (i : Int), In i l -> 0 <= ⟦ i ⟧ < Z.of_nat n)
    -> (forall (p : (Int * Int)), In p (index l) -> 0 <= ⟦ fst p ⟧ < Z.of_nat n).
Proof.
  unfold index.
  eauto using indexPreservesBound'.
Qed.

Lemma indexAllInBounds : forall (l : list Int),
    let n := length l in
    (forall (i : Int), In i l -> 0 <= ⟦ i ⟧ < Z.of_nat n) ->
    allInBounds (map denoteIntTuple (index l)).
Proof.
  intros. unfold allInBounds, inBounds. intros.
  apply in_map_iff in H0.
  destruct H0.
  destruct p, x.

  rewrite map_length. rewrite indexLength.
  destruct H0.
  unfold denoteIntTuple in H0.
  inversion H0. subst. clear H0.
  split.
  * eapply indexPreservesBound with (p := (_, _)); eauto.
  * eapply indexBounds with (p := (_, _)); eauto.
Qed.

Theorem solveNQueensSound : forall (n : nat) (l : list (Int * Int)),
    solveNQueens n = solution l -> correct n (map denoteIntTuple l).
Proof.
  intros.
  unfold correct.
  unfold solveNQueens in H.
  apply searchSolution in H.
  space_crush.
  break_if; space_crush.

  assert (length x = n) by eauto using nListSpaceLength.
  subst.

  apply isLegalIffNoCollisions in Heqb.
  eauto using indexAllInBounds, nListSpaceRangeBounds.
Qed.

Lemma distinctPermutation {A} : forall (l1 l2 : list A),
    Permutation l1 l2 -> distinct' l1 -> distinct' l2.
Proof.
  intros l1 l2.
  rewrite !distinct'_iff_NoDup.
  apply Permutation_NoDup.
Qed.

Lemma permutationNoCollisions : forall (l1 l2 : list (Z*Z)),
    Permutation l1 l2 -> noCollisions l1 -> noCollisions l2.
Proof.
  intros l1 l2 H.
  rewrite !noCollisionsIffDistinct.
  intuition eauto using distinctPermutation, Permutation_map.
Qed.

Lemma permutationIsLegal : forall (l1 l2 : list (Int * Int)),
    Permutation l1 l2 -> isLegal l1 = true -> isLegal l2 = true.
Proof.
  intros l1 l2 H.
  rewrite !isLegalIffNoCollisions.
  eauto using permutationNoCollisions, Permutation_map.
Qed.

Lemma permutationCorrect' : forall (l1 l2 : list (Z*Z)) (n : nat),
    Permutation l1 l2 -> correct n l1 -> correct n l2.
Proof.
  unfold correct, allInBounds.
  intros.
  erewrite <- Permutation_length by eauto.
  intuition idtac.
  - eauto using Permutation_in, Permutation_sym.
  - eauto using permutationNoCollisions.
Qed.

Lemma permutationCorrect : forall (l1 l2 : list (Int*Int)) (n : nat),
    Permutation l1 l2
    -> correct n (map denoteIntTuple l1) -> correct n (map denoteIntTuple l2).
Proof.
  eauto using permutationCorrect', Permutation_map.
Qed.

Local Notation zToInt := fromZ.
Local Notation zToIntOk := denoteFromZOk.

Lemma zToIntZeroOk : zToInt 0 = zero.
  apply denoteInjective.
  space_crush.
Qed.

Lemma zToIntOneOk : zToInt 1 = one.
  apply denoteInjective.
  space_crush.
Qed.

Lemma zToIntPlusOk : forall (i j : Z), zToInt (i + j) = plus (zToInt i) (zToInt j).
  intros.
  apply denoteInjective.
  space_crush.
Qed.

Lemma zToIntEqualOk : forall (i j : Z),
    equal (zToInt i) (zToInt j) = Z.eqb i j.
Proof.
  space_crush.
Qed.

Lemma zToIntLeOk : forall (i j : Z),
    le (zToInt i) (zToInt j) = Z.leb i j.
Proof.
  space_crush.
Qed.

Definition zTupleToIntTuple (p : Z*Z) : (Int*Int) :=
  let '(x, y) := p in (zToInt x, zToInt y).

Lemma indexPreservesFst' {A} : forall (l : list A) i, map fst (index' i l) = l.
Proof.
  induction l; simpl; intros; congruence.
Qed.

Lemma indexPreservesFst {A} : forall (l : list A), (map fst (index l)) = l.
Proof.
  intros.
  apply indexPreservesFst'.
Qed.

Fixpoint countUp (n : nat) (start : Int) : list Int :=
  match n with
  | S n' => start :: countUp n' (plus one start)
  | O => []
  end.

Lemma sndIndexCountsUp' {A} : forall (l : list A) (i : Int),
    map snd (index' i l) = countUp (length l) i.
Proof.
  induction l; simpl; intros; congruence.
Qed.

Lemma sndIndexCountsUp {A} : forall (l : list A) (n : nat),
    length l = n -> map snd (index l) = countUp n zero.
Proof.
  intros.
  subst.
  apply sndIndexCountsUp'.
Qed.

Lemma sndIndex' {A} :
  forall (l : list (A * Int)) i,
      map snd l = countUp (length l) i ->
      index' i (map fst l) = l.
Proof.
  induction l; simpl; intros.
  - auto.
  - destruct a; simpl in *.
    f_equal.
    + congruence.
    + apply IHl. congruence.
Qed.

Lemma sndIndex {A} : forall (l : list (A*Int)),
    map snd l = countUp (length l) zero -> index (map fst l) = l.
Proof.
  unfold index.
  eauto using sndIndex'.
Qed.

Lemma intToZInvolutive : forall (p : Z*Z),
    denoteIntTuple (zTupleToIntTuple p) = p.
Proof.
  intros. destruct p. simpl.
  auto using f_equal2, zToIntOk.
Qed.

Lemma intToZInvolutiveMap : forall (l : list (Z*Z)),
    map denoteIntTuple (map zTupleToIntTuple l) = l.
Proof.
  intros.
  rewrite map_map.
  rewrite map_ext with (g := id).
  - apply map_id.
  - apply intToZInvolutive.
Qed.

Lemma intSndToZSnd : forall (l : list (Z*Z)),
    map snd (map zTupleToIntTuple l) = map zToInt (map snd l).
Proof.
  intros.
  rewrite !map_map.
  apply map_ext.
  destruct a; reflexivity.
Qed.

Lemma zToIntInj : forall (z1 z2 : Z),
    zToInt z1 = zToInt z2 -> z1 = z2.
Proof.
  intros.
  apply f_equal with (f := denote) in H.
  space_crush.
Qed.

Lemma zToIntMapInj : forall (l1 l2 : list Z),
    map zToInt l1 = map zToInt l2 -> l1 = l2.
Proof.
  eauto using map_inj, zToIntInj.
Qed.

Lemma zToIntMapBij : forall (l1 l2 : list Z),
    map zToInt l1 = map zToInt l2 <-> l1 = l2.
Proof.
  intros. split; intros.
  * auto using zToIntMapInj.
  * congruence.
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
  * cbn [countUp zCountUp map].
    rewrite IHn.
    space_crush.
Qed.

Lemma sortedBySecond : forall (l : list (Z*Z)),
    Sorted.LocallySorted (fun p1 p2 => is_true (leb (snd p1) (snd p2))) l
    -> Sorted.LocallySorted (fun z1 z2 => is_true (leb z1 z2)) (map snd l).
Proof.
  intros; induction H; simpl; constructor; try assumption.
Qed.

Theorem sortDistinctListRangeGeneral : forall (l : list Z) (n : nat) (i : Z),
    Sorted.StronglySorted Z.le l
    -> length l = n
    -> NoDup l
    -> (forall z, In z l -> i <= z < i + Z.of_nat n)
    -> l = zCountUp n i.
Proof.
  intros l n i H. revert n i.
  induction H; simpl; intros n i ? ND Range; subst.
  * reflexivity.
  * rename H0 into AleL.
    cbn [zCountUp].
    invc ND. rename H2 into Nin. rename H3 into ND.

    assert (i <= a) by (apply Range; auto).

    assert (forall z, In z l -> a < z) as Alt.
    {
      intros z Hin.
      apply Z.le_neq.
      split.
      - eapply Forall_forall; eauto.
      - congruence.
    }

    assert (forall z : Z, In z l -> 1 + i <= z < (1 + i) + Z.of_nat (length l)) as Range'.
    {
      intros z Hin.
      pose proof (Range _ (or_intror Hin)).
      apply Alt in Hin.
      lia.
    }
    specialize (IHStronglySorted (length l) (1 + i) eq_refl ltac:(auto) Range').
    rewrite <- IHStronglySorted.

    f_equal.
    destruct l as [|b l].
    + specialize (Range _ (or_introl eq_refl)). simpl in Range. omega.
    + assert (b = 1 + i) by (cbn [length zCountUp] in IHStronglySorted; congruence).
      assert (a < b) by intuition.
      omega.
Qed.

Lemma LocallySorted_ext : forall A (R1 R2 : A -> A -> Prop),
    (forall x y, R1 x y <-> R2 x y) ->
    forall l, Sorted.LocallySorted R1 l -> Sorted.LocallySorted R2 l.
Proof.
  intros A R1 R2 HR l H.
  induction H; constructor; firstorder.
Qed.

Lemma sortDistinctListRange : forall (l : list Z) (n : nat),
    length l = n
    -> distinct' l -> (forall z, In z l -> 0 <= z < Z.of_nat n)
    -> Sorted.LocallySorted (fun z1 z2 => is_true (leb z1 z2)) l
    -> l = zCountUp n 0.
Proof.
  intros. apply sortDistinctListRangeGeneral; auto.
  - apply Sorted.Sorted_StronglySorted. red. intros. omega.
    apply Sorted.Sorted_LocallySorted_iff.
    eapply LocallySorted_ext; [|eauto].
    simpl. intros. rewrite leb_le. intuition.
  - now rewrite <- distinct'_iff_NoDup.
Qed.

Lemma sortedIndex : forall (p : list (Z*Z)) (n : nat),
    correct n p ->
    map zTupleToIntTuple (sort p)
    = index (map fst (map zTupleToIntTuple (sort p))).
Proof.
  intros.
  assert (Permutation p (sort p)) by (apply Permuted_sort).
  destruct H as (? & IB & NC).
  apply noCollisionsIffDistinct in NC.
  rewrite sndIndex.
  * reflexivity.
  * rewrite map_length.
    erewrite <- Permutation_length by eauto.
    rewrite intSndToZSnd. rewrite countUpToZCountUp. rewrite zToIntMapBij.
    rewrite denoteZeroOk.
    apply sortDistinctListRange.
    + rewrite map_length. auto using Permutation_length, Permutation_sym.
    + intuition eauto using distinctPermutation, Permutation_map.
    + intros. unfold allInBounds in *. unfold inBounds in *.
      apply in_map_iff in H1.
      destruct H1 as ([x y] & ? & Hin). simpl in *. subst.
      eapply Permutation_in in Hin.
      apply IB in Hin. intuition.
      auto using Permutation_sym.
    + apply sortedBySecond.
      apply Sorted_sort.
Qed.

Lemma if_true :
  forall A b (x y : A), b = true -> (if b then x else y) = x.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma inRangeIfInBounds : forall (z : Z) (n : nat),
    0 <= z < Z.of_nat n -> Ensembles.In ⟦ range zero (natToInt n) ⟧ (zToInt z).
Proof.
  intros.
  unfold range.
  space_crush.
  exists (zToInt z).
  split; space_crush.
  rewrite if_true; space_crush.
Qed.

Lemma inNListSpaceIfInSpace {A} : forall (l : list A) (s : Space A) (n : nat),
    length l = n ->
    (forall a, In a l -> Ensembles.In ⟦ s ⟧ a) -> Ensembles.In ⟦ nListSpace s n ⟧ l.
Proof.
  induction l; intros; subst; simpl in *; space_crush.
  exists l.
  split; space_crush.
  exists a.
  space_crush.
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
  exists (sort p).
  assert (Permutation p (sort p)) by apply Permuted_sort.
  split; [assumption|].
  space_crush.
  assert (correct n (sort p)) by eauto using permutationCorrect'.
  exists (map fst (map zTupleToIntTuple (sort p))).
  split.
  * destruct H1 as (L & A & NC).
    apply inNListSpaceIfInSpace; [now rewrite !map_length|].
    intros a.
    rewrite in_map_iff.
    intros [[x1 y1]]. simpl. intros (?). subst a.
    rewrite in_map_iff.
    intros [[x2 y2]]. simpl. intros (E). inversion E; subst; clear E.
    intro Hin.

    apply inRangeIfInBounds.
    apply A in Hin.
    destruct Hin.
    assumption.
  * erewrite <- sortedIndex by eauto.
    rewrite (proj2 (isLegalIffNoCollisions _))
      by (rewrite intToZInvolutiveMap; unfold correct in *; intuition).
    space_crush.
Qed.

Theorem solveNQueensComplete : forall (n : nat),
    solveNQueens n = uninhabited -> ~exists l, correct n l.
Proof.
  intros.
  intro H'.
  destruct H' as [l C].
  apply correctArrangementsInIndex in C.
  destruct C as (l' & P & H1).
  rewrite searchUninhabited in H1 by auto.
  inversion H1.
Qed.

Definition solver {A} (P : A -> Prop) := {a | P a} + {~exists a, P a}.

Definition solveNQueensDep n : option (solver (correct n)).
  destruct (solveNQueens n) as [l| | ] eqn:eq.
  - (* solution *)
    refine (Some _).
    left.
    exists (map denoteIntTuple l).
    apply solveNQueensSound.
    assumption.
  - (* unihabited *)
    refine (Some _).
    right.
    apply solveNQueensComplete.
    assumption.
  - (* unknown, this should never happen, because we only deal with
    integers in finite ranges *)
    refine None.
Defined.

End Queens.

Require Import Rosette.Quantified.

Definition solveNQueensRosette := solveNQueensDep.

Extraction Language Scheme.
Extraction "queens" solveNQueensRosette.
