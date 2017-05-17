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

(* Convert various boolean things to Propositional things, eg && becomes /\, etc. *)
Ltac do_bool :=
  repeat
    match goal with
    | [ H : _ && _ = true |- _ ] => apply andb_true_iff in H; destruct H
    | [ H : _ || _ = false |- _ ] => apply orb_false_iff in H; destruct H
    | [ H : negb _ = true |- _ ] => apply negb_true_iff in H
    | [ H : context [(_ <=? _) = true] |- _ ] => rewrite Z.leb_le in H
    | [ H : context [(_ <? _) = true] |- _ ] => rewrite Z.ltb_lt in H
    | [ |- context [_ && _ = true] ] => rewrite andb_true_iff
    | [ |- context [_ || _ = false] ] => rewrite orb_false_iff
    | [ |- context [negb _ = true] ] => rewrite negb_true_iff
    | [ |- context [(_ <=? _) = true] ] => rewrite Z.leb_le
    | [ |- context [(_ <? _) = true] ] => rewrite Z.ltb_lt
    end.
