Require Import ListEx.
Require Import Basic.
Require Import Minus.
Require Import EqDec.
Require Import Precise.

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

Global Instance listSearch : Search.
  refine {| 
    Precise.search A l := match l with 
                          | [] => uninhabited 
                          | a :: _ => solution a 
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

Fixpoint removeList {A} `{eqDec A} (l1 l2 : list A) : list A :=
  match l2 with
  | [] => l1
  | h :: t => remove eqDecide h (removeList l1 t)
  end.

Lemma In_remove_other {A} `{eqDec A} : forall (x1 x2 : A) (l1 : list A),
    x1 <> x2 -> (In x1 l1 <-> In x1 (remove eqDecide x2 l1)).
Proof.
  split; intros.
  - induction l1; simpl in *; try contradiction.
    destruct H1 as [H2 | H2];
      destruct (eqDecide x2 a) as [H3 | H3];
      simpl; try (rewrite H2 in H3); intuition.
  - induction l1; simpl in *; try contradiction.
    destruct (eqDecide x2 a) as [H2 | H2];
      try (destruct H1); intuition.
Qed.

Lemma In_removeList {A} `{eqDec A} : forall (x : A) (l1 l2 : list A),
    In x (removeList l1 l2) <-> In x l1 /\ ~In x l2.
Proof.
  split; intros.
  - induction l2; simpl; intros.
    * split; intuition. 
    * destruct (eqDecide a x) as [H' | H']; simpl in H0.
      + rewrite H' in H0.
        apply remove_In in H0.
        contradiction.
      + assert (In x (removeList l1 l2)) as H'' by (apply In_remove_other in H0; intuition).
        apply IHl2 in H''.
        destruct H'' as [H'1  H'2].
        split; intuition.
  - destruct H0 as [H0  H1].
    induction l2; try intuition.
    simpl in *.
    destruct (eqDecide a x) as [H3 | H3]; try intuition.
    apply In_remove_other; intuition.
Qed.

Global Instance listMinus : Minus.
idtac.
simple refine {|
    minus := @removeList
  |}.
cbn.
unfold Setminus.
destruct t; intro H0; apply Extensionality_Ensembles; simpl.
- split; intros; intuition.
- split.
  * intros x H'. destruct (eqDecide x a) as [H1 | H1].
    + split; rewrite H1 in H'; apply remove_In in H'; contradiction.
    + apply In_remove_other in H'; auto.
      apply In_removeList in H'. destruct H' as [H2 H3].
      split; try intuition.
  * intros. destruct H as [H1 H2].
    assert (a <> x /\ ~In x t) as H3 by (split; firstorder).
    clear H2.
    destruct H3 as [H2 H3].    
    apply In_remove_other; try intuition.
    apply In_removeList.
    split; auto.
Defined.