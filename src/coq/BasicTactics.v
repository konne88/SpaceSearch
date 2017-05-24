Require Import ZArith Bool.

Local Open Scope Z.

(*** Convenience Tactics ***)

(* Excerpted from StructTact, see: https://github.com/uwplse/StructTact/ *)

Ltac inv H := inversion H; subst.
Ltac invc H := inversion H; subst; clear H.

(* Find something of the form `if foo then ... else ...` and destruct foo. *)
Ltac break_if :=
  match goal with
  | [ H : context [if ?X then _ else _] |- _ ] => destruct X eqn:?
  | [ |- context [if ?X then _ else _] ] => destruct X eqn:?
  end.

(* Find something of the form `match foo with ... end` and destruct foo. *)
Ltac break_match :=
  match goal with
  | [ H : context [match ?X with _ => _ end] |- _ ] => destruct X eqn:?
  | [ |- context [match ?X with _ => _ end] ] => destruct X eqn:?
  end.

Lemma implb_true_iff : forall b1 b2,
      implb b1 b2 = true <->
      (b1 = true -> b2 =true).
Proof.
  destruct b1, b2; simpl; intuition congruence.
Qed.

Hint Rewrite andb_true_iff orb_true_iff negb_true_iff implb_true_iff : bool.
Hint Rewrite andb_false_iff orb_false_iff negb_false_iff : bool.
Hint Rewrite Z.leb_le Z.ltb_lt : bool.

(* Convert various boolean things to Propositional things, eg && becomes /\, etc. *)
Ltac do_bool :=
  autorewrite with bool in *.