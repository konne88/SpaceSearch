Require Import Basic.
Require Import Rosette.Quantified.
Require Import ListEx.
Require Import Native.
Require Import Bool.
Require Import Arith.EqNat.
Require Import Integer.

Class eqDec A := {
  eqDecide : forall (a a':A), {a=a'} + {a<>a'}
}.

Notation "a =? b" := (eqDecide a b).

Global Instance eqDecNat : eqDec nat.
  constructor. decide equality.
Defined.

Global Instance eqDecProd {A B} `{eqDec A} `{eqDec B} : eqDec (A * B).
  constructor.
  intros.
  destruct a as [a b].
  destruct a' as [a' b'].
  (* I'm branching on b first, because that's what I need in bagpipe :( *)
  destruct (b =? b'). 
  - destruct (a =? a').
    + left. congruence.
    + right. congruence.
  - right. congruence.
  (* constructor; repeat decide equality; apply eqDecide.  *)
Defined.

Existing Instance rosetteBasic.
Existing Instance rosetteSearch.

Axiom ADMIT : forall A, A.

Global Instance eqDecInteger `{Integer} : eqDec Int := {|
  eqDecide := _
|}.
  intros n m.
  destruct (equal n m) eqn:eq.
  - left.
    rewrite denoteEqualOk in eq.
    rewrite Z.eqb_eq in eq. 
    apply ADMIT.
  - right.
    apply ADMIT.
Defined.

Definition elem {A} `{eqDec A} (a:A) : list A -> bool :=
  existsb (fun a' => if a =? a' then true else false).

Fixpoint distinct {A} `{eqDec A} (l:list A) : bool :=
  match l with
  | a :: l => andb (negb (elem a l)) (distinct l)
  | [] => true
  end.

Definition uncurry {A B C} (f:A->B->C) (ab:A*B) : C :=
  f (fst ab) (snd ab).

Definition isLegal (queens : list (Int * Int)) : bool :=
  forallb (fun x => x) [
    distinct (map fst queens);
    distinct (map snd queens);
    distinct (map (uncurry plus) queens);
    distinct (map (uncurry minus) queens)
  ].

Definition lt (n m:Int) : bool := 
  andb (le n m) (negb (if n =? m then true else false)).

Definition nNat (n:Int) : Space Int.
  refine (bind full (fun v : Int => _)).
             (*    0 <= v < n *)
  refine (if (andb (le zero v) (lt v n))
          then single v else empty).
Defined.

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

Compute (index [false; true]).

Fixpoint natToInt (n:nat) : Int :=
  match n with
  | O => zero
  | S n => plus one (natToInt n)
  end.

Definition solveNQueens (n:nat) : Result (list (Int * Int)).
  refine (
  search (
    bind (nListSpace (nNat (natToInt n)) n) 
         (fun xs:list Int => _))).
  refine (let ps := index xs in _).
  refine (if isLegal ps then single ps else empty).
Defined.

Extraction Language Scheme.

Extraction "queens" solveNQueens.
