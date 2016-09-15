Require Import SpaceSearch.
Require Import EnsemblesEx.
Require Import List.
Import ListNotations.

Export List.
Export ListNotations.

Fixpoint concat {A} (l : list (list A)) : list A :=
  match l with
  | [] => []
  | h::t => h ++ concat t
  end.

Instance denoteListToEnsemble {A} : Denotation (list A) (Ensemble A) := {|
  denote l := fun a => In a l
|}.

Instance listSpaceSearch : SpaceSearch.
  refine {|
    Space := list;
    empty A := [];
    single A a := [a];
    union A l l' := l ++ l';
    bind A B S f := concat (map f S);
    search A l := l
  |}.
Proof.
  - intros. 
    rewrite emptyIsFalse.
    reflexivity.
  - intros. 
    rewrite singletonIsEqual.
    apply Extensionality_Ensembles.
    simpl.
    split.
    + intros ? []; intros []; constructor.
    + intros ? [].
      left.
      reflexivity.
  - intros. 
    rewrite unionIsOr.
    apply Extensionality_Ensembles'; intros a.
    simpl.
    rewrite in_app_iff.
    reflexivity.
  - intros A B l f.
    apply Extensionality_Ensembles'; intros b.
    rewrite bigUnionIsExists.
    split.
    * intro h.
      induction l.
      + compute in h.
        intuition.
      + simpl in h.
        rewrite in_app_iff in *.
        destruct h. {
          exists a.
          simpl.
          intuition.
        } {
          specialize (IHl H).
          destruct IHl as [a' []].
          exists a'.
          simpl in *.
          intuition.
        }
    * intro h.
      simpl in *.
      destruct h as [a [al bfa]].
      induction l as [|a'].
      + compute in *.
        intuition.
      + simpl in *.
        rewrite in_app_iff.
        destruct al. {
          left.
          subst.
          intuition.
        } {
          right.
          intuition.
        }
  - intros ? [] ? h.
    + destruct h.
    + simpl in *.
      assumption.
  - intros ? [] h.
    + rewrite emptyIsFalse.
      reflexivity.
    + inversion h.
Defined.
