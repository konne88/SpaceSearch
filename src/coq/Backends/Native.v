Require Import ListEx.
Require Import Basic.
Require Precise.

Export ListEx.

Global Instance denoteListToEnsemble {A} : Denotation (list A) (Ensemble A) := {|
  denote l := fun a => In a l
|}.

Global Instance listSpace : Basic.
  refine {|
    Space := list;
    empty A := [];
    single A a := [a];
    union A l l' := l ++ l';
    bind A B S f := concat (map f S)
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
Defined.

Global Instance listSearch : Precise.Search.
  refine {| 
    Precise.search A l := match l with 
                          | [] => Precise.empty 
                          | a :: _ => Precise.solution a 
                          end
  |}.
  - intros ? [] ? h.
    + congruence.
    + simpl in *.
      left.
      congruence.
  - intros ? [] h.
    + rewrite emptyIsFalse.
      reflexivity.
    + inversion h.
Defined.

Lemma listMapEqMap {A B l} {f:A->B} : Basic.map f l = List.map f l.
  induction l.
  - reflexivity.
  - simpl in *.
    congruence.
Qed.

