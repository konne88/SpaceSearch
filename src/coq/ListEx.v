Require Import SpaceSearch.
Require Import EnsemblesEx.
Require Import List.
Import ListNotations.

Export List.
Export ListNotations.

Notation "f <$> l" := (map f l) (at level 35).

Fixpoint concat {A} (l : list (list A)) : list A :=
  match l with
  | [] => []
  | h::t => h ++ concat t
  end.

Lemma concatIn {A} {a:A} l {L} : In a l -> In l L -> In a (concat L).
  intros.
  induction L as [|l' L'].
  + contradiction.
  + simpl.
    apply in_or_app.
    cbn in *.
    intuition.
    subst.
    intuition.
Qed.

Lemma concat_app {A} {l l':list (list A)} : concat (l ++ l') = concat l ++ concat l'.
  induction l.
  - cbn. reflexivity.
  - cbn in *.
    rewrite IHl.
    rewrite app_assoc.
    reflexivity.
Defined.

