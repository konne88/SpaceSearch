Require Import Basic.
Require Import Rosette.Quantified.
Require Import ListEx.
Require Import Native.
Require Import Bool.
Require Import Arith.EqNat.
Require Import Integer.
Require Import EqDec.

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
