Require Import SpaceSearch.
Require Import Rosette.
Require Import ListEx.
Require Import Bool.
Require Import Arith.EqNat.

Fixpoint distance (n m:nat) : nat :=
  match n, m with
  | S n, S m => distance n m
  | O, _ => m
  | _, O => n
  end.

Definition isSafe (x y x' y':nat) : bool :=
  (beq_nat x x' && beq_nat y y') ||
  (negb (
    (beq_nat x x') || (* vertical *)
    (beq_nat y y') || (* horizontal *)
    (beq_nat (distance x x') (distance y y')))). (* diagonal *)

Compute (isSafe 0 0 0 0).
Compute (isSafe 0 1 1 0).

Fixpoint nNat `{SpaceSearch} (n:nat) : Space nat :=
  match n with
  | 0%nat => empty
  | S n => union (nNat n) (single n) 
  end.

Compute (@nNat listSpaceSearch 3).

Fixpoint nListSpace `{SpaceSearch} {A} (s:Space A) (n:nat) : Space (list A) :=
  match n with
  | 0%nat => single []
  | S n => bind (nListSpace s n) (fun l => 
          bind s (fun a => single (a :: l)))
  end.

Compute (@nListSpace listSpaceSearch nat (nNat 2) 3).

Definition index {A} : list A -> list (A * nat) :=
  let fix rec n l :=
    match l with
    | [] => []
    | a::l => (a,n) :: rec (S n) l
    end 
  in rec 0.

Compute (index [false; true]).

Existing Instance rosette.

Definition listToOption {A} (l:list A) : option A :=
  match l with
  | [] => None
  | a::_ => Some a 
  end.

Definition solveNQueens (n:nat) : option (list nat) :=
  listToOption (search (
    bind (nListSpace (nNat n) n) (fun xs:list nat =>
      let ps := index xs in
      if forallb (fun p =>
         forallb (fun q => 
           isSafe (fst p) (snd p) (fst q) (snd q)) ps) ps
      then single xs 
      else empty))).

Extraction Language Scheme.

Extraction "queens" solveNQueens.
