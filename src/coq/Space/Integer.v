Require Import Basic.
Require Import Full.
Require Import ZArith.
Require Import EqDec.
Require ListEx.

Export ZArith.

Open Scope Z.

Class Integer `{Basic} := { 
  Int : Type;
  denotationInt :> Denotation Int Z;
  fullInt :> Full Int;

  fromZ : Z -> Int;
  plus : Int -> Int -> Int;
  minus : Int -> Int -> Int;
  equal : Int -> Int -> bool;
  le : Int -> Int -> bool;

  denoteFromZOk z : ⟦fromZ z⟧ = z;
  denotePlusOk n m : ⟦plus n m⟧ = ⟦n⟧ + ⟦m⟧;
  denoteMinusOk n m : ⟦minus n m⟧ = ⟦n⟧ - ⟦m⟧;
  denoteEqualOk n m : equal n m = (⟦ n ⟧ =? ⟦ m ⟧);
  denoteLeOk n m : le n m = (⟦ n ⟧ <=? ⟦ m ⟧);
  denoteInjective n m : ⟦n⟧ = ⟦m⟧ -> n = m
}.

Section Integer.
  Context `{Integer}.

  Definition mone : Int := fromZ (-1).
  Definition zero := fromZ 0.
  Definition one  := fromZ 1.

  Lemma denoteMoneOk : ⟦mone⟧ = -1.
    apply denoteFromZOk.
  Qed.

  Lemma denoteZeroOk : ⟦zero⟧ = 0.
    apply denoteFromZOk.
  Qed.

  Lemma denoteOneOk : ⟦one⟧ = 1.
    apply denoteFromZOk.
  Qed.
End Integer.

Section Definitions.
  Context `{Basic}.
  Context `{Integer}.
  
  Global Instance eqDecInteger : eqDec Int := {|
    eqDecide := _
  |}.
    intros n m.
    destruct (equal n m) eqn:eq.
    - left.
      rewrite denoteEqualOk in eq.
      rewrite Z.eqb_eq in eq. 
      apply denoteInjective.
      assumption.
    - right.
      rewrite denoteEqualOk in eq.
      rewrite Z.eqb_neq in eq.
      congruence.
  Defined.
  
  Fixpoint natToInt (n:nat) : Int :=
    match n with
    | O => zero
    | S n => plus one (natToInt n)
    end.
  
  Definition lt (n m:Int) : bool := 
    andb (le n m) (negb (equal n m)).

  Lemma denoteLtOk n m : lt n m = (⟦ n ⟧ <? ⟦ m ⟧).
  Proof.
    unfold lt.
    rewrite denoteLeOk.
    apply Bool.eq_true_iff_eq.
    rewrite Bool.andb_true_iff, Bool.negb_true_iff.
    rewrite denoteEqualOk.
    rewrite Z.leb_le, Z.eqb_neq, Z.ltb_lt.
    omega.
  Qed.

  Lemma fromZInv : forall (i : Int), fromZ ⟦ i ⟧ = i.
    intros.
    apply denoteInjective.
    now rewrite denoteFromZOk.
  Qed.

  (* { v | n <= v < m } *)
  Definition range (n m:Int) : Space Int.
    refine (bind full (fun v : Int => _)).
    refine (if (andb (le n v) (lt v m))
            then single v else empty).
  Defined.

  Definition countUp (n : nat) (start : Int) : list Int :=
    ListEx.tabulate (plus one) n start.

  Definition zCountUp (n : nat) (start : Z) : list Z :=
    ListEx.tabulate (Z.add 1) n start.

  Lemma countUpToZCountUp : forall (n : nat) (start : Int),
      countUp n start = List.map fromZ (zCountUp n ⟦ start ⟧).
  Proof.
    intros.
    unfold countUp, zCountUp.
    apply ListEx.tabulate_map.
    intros.
    - apply denoteInjective.
      now rewrite denotePlusOk, denoteOneOk, !denoteFromZOk.
    - now rewrite fromZInv.
  Qed.
End Definitions.

