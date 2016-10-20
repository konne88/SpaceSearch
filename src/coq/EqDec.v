(* excerpted from https://github.com/konne88/CoqStdlib/blob/master/EqDec.v *)

Require Import NArith.
Require Import Arith.
Require Import Bool.
Require Import List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Equality.
Require Import List.
Require Import Ascii.
Require Import String.
Import EqNotations.

Class eqDec A := {
  eqDecide : forall (a a':A), {a=a'} + {a<>a'}
}.

Notation "a =? b" := (eqDecide a b).
