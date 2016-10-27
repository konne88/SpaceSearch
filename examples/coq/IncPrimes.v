Require Import Basic.
Require Import EqDec.
Require Import Minus.
Require Import Incremental.
Require Import ListEx.
Require Import Rosette.Unquantified.
Require Import Native.
Require Import Bool.
Require Import EqNat.
Require Import Nat.

Open Scope nat.

(* A very simple test case for nats to demonstrate
   work saved by incremental serarch *)

(* purposely dumb, slow, bad primality test *)
Definition isPrime (n: nat) : bool :=
  let aux :=
      fix hasFactor n t :=
        match t with
        | 0 | 1 => false
        | S t' =>
          if (n / t) * t =? n then true
          else hasFactor n t'
        end
  in
  match n with
  | 0%nat => false (* undefined *)
  | 1%nat => false (* undefined *)
  | S n' => negb (aux n n')
  end.

Compute (fold_left (fun b n => andb b (isPrime n))
            [2; 3; 5; 7; 11; 13; 17; 19] true).

Compute (fold_left (fun b n => andb b (negb (isPrime n)))
            [4; 6; 8; 9; 10; 12; 14; 15; 16; 18; 20] true).

Definition evensAfterTwo (n : nat) : list nat :=
  let aux := (fix buildList n acc :=
     match n with
     | 0 => acc
     | S n' =>
       match acc with
       | [] => buildList n' [4]
       | h :: _ => buildList n' (2+h :: acc)
       end
     end) in
  rev (aux n []).

Compute evensAfterTwo 100.

Definition evenSpace `{Basic} (n : nat) : Space nat :=
  let aux := (fix spaceOf l acc :=
                match l with
                | [] => acc
                | h :: t => spaceOf t (union (single h) acc)
                end) in
  let evens := evensAfterTwo n in
  aux evens empty.

Compute (@evenSpace listSpace 5).

Existing Instance rosetteSearch.

Definition listToOption {A} (l:list A) : option A :=
  match l with
  | [] => None
  | a::_ => Some a 
  end.

Definition testSpace (n : nat) : Space nat :=
  if isPrime n then single n else empty.

Definition primeSearch (n : nat) : Result nat :=
  search (bind (evenSpace n) testSpace).

Extraction Language Scheme.

Extraction "primes-naive" primeSearch.

Definition primeIncSearch `{eqDec nat} (n : nat) : Result nat :=
  let evens := evenSpace n in
  incSearch
    (bind (union evens (single 3)) testSpace)
    (bind evens testSpace).

Extraction Language Scheme.

Extraction "primes-incremental" primeIncSearch.