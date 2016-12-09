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

Global Instance eqDecSigT {A B} `{eqDec A} `{forall a:A, eqDec (B a)} : eqDec {a:A & B a}.
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

Global Instance eqDecSigT' {A B} `{eqDec A} `{forall a:A, eqDec (B a)} : eqDec (sigT B).
  apply eqDecSigT.
Defined.

Global Instance eqDecSum {A B} `{eqDec A} `{eqDec B} : eqDec (A + B).
  constructor.
  decide equality; apply eqDecide.
Defined.

Global Instance eqDecList {A} `{eqDec A} : eqDec (list A).
  constructor.
  intros.
  apply list_eq_dec.
  apply eqDecide.
Defined.

Global Instance eqDecBool : eqDec bool.
  constructor.
  decide equality.
Defined.

Global Instance eqDecUnit : eqDec unit.
  constructor.
  decide equality.
Defined.

Global Instance eqDecZ : eqDec Z.
  constructor.
  decide equality;
  decide equality.
Defined.

Global Instance eqDecAscii : eqDec ascii.
  constructor.
  apply ascii_dec.
Defined.

Global Instance eqDecString : eqDec string.
  constructor.
  apply string_dec.
Defined.
