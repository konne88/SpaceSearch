Require Import Basic.
Require Import Places.

Extraction Language Scheme.

(* define the worker functions *)

Parameter squareWorker : Worker nat nat.
Definition square (n:nat) : nat := n * n.
Extract Constant squareWorker => "'square".

Extract Constant Worker "a" "b" => "__".
Extract Constant denoteWorker => "(lambdas (_ n) (square n))".

Extraction "worker" denoteWorker square.

(* define the distributed computation *)

Fixpoint enumerate (n:nat) : Space nat.
  refine (match n with
  | 0 => []
  | S n => n :: enumerate n
  end).
Defined.

Example enumerateFive : enumerate 5 = [4;3;2;1;0]. reflexivity. Qed.

Definition squareList (n:nat) : list nat.
  refine (search (enumerate n) squareWorker).
Defined.

Extraction "parallel-test" squareList square.
