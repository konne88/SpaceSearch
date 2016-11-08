Require Import Basic.
Require Import Full.
Require Import ZArith.
Require Import EqDec.

Export ZArith.

Open Scope Z.

Class Integer `{Basic} := { 
  Int : Type;
  denotationInt :> Denotation Int Z;
  fullInt :> Full Int;

  mone : Int;
  zero : Int;
  one : Int;
  plus : Int -> Int -> Int;
  minus : Int -> Int -> Int;
  equal : Int -> Int -> bool;
  le : Int -> Int -> bool;

  denoteMoneOk : ⟦mone⟧ = -1;
  denoteZeroOk : ⟦zero⟧ = 0;
  denoteOneOk : ⟦one⟧ = 1;
  denotePlusOk n m : ⟦plus n m⟧ = ⟦n⟧ + ⟦m⟧;
  denoteMinusOk n m : ⟦minus n m⟧ = ⟦n⟧ - ⟦m⟧;
  denoteEqualOk n m : equal n m = (⟦ n ⟧ =? ⟦ m ⟧);
  denoteLeOk n m : le n m = (⟦ n ⟧ <=? ⟦ m ⟧);
  denoteInjective n m : ⟦n⟧ = ⟦m⟧ -> n = m
}.

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

  (* { v | n <= v < m } *)
  Definition range (n m:Int) : Space Int.
    refine (bind full (fun v : Int => _)).
    refine (if (andb (le n v) (lt v m))
            then single v else empty).
  Defined.
End Definitions.

