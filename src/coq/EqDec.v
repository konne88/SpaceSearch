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
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Sumbool.
Import EqNotations.
Require Import Arith.
Require Import CpdtTactics.

Class eqDec A := {
  eqDecide : forall (a a':A), {a=a'} + {a<>a'}
}.

Notation "a =? b" := (eqDecide a b).

Global Instance eqDecNat : eqDec nat.
  constructor. decide equality.
Defined.

Global Instance eqDecProd {A B} `{eqDec A} `{eqDec B} : eqDec (A * B).
  constructor; repeat decide equality; apply eqDecide.
Defined.

Instance eqDecSigT {A B} `{eqDec A} `{forall a:A, eqDec (B a)} : eqDec {a:A & B a}.
  constructor. intros x x'. 
  destruct x.
  destruct x'.
  match goal with a:A, a':A |- _ => destruct (a =? a') end.
  - subst. 
    match goal with a:A, b:B ?a, b':B ?a |- _ => destruct (b =? b') end.
    + left.
      subst.
      reflexivity.
    + right. 
      crush.
  - right. 
    injection.
    congruence.
Defined.
