Require Import ListEx.
Require Import Basic.
Require Import Minus.
Require Import EqDec.
Require Import Precise.
Require Import Incremental.
Require Import Bind.

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
  | h :: t => removeList (remove eqDecide h l1) t
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
  split; revert x l1.
  - induction l2; simpl; intros.
    * split; intuition. 
    * destruct (eqDecide a x) as [H' | H']; simpl in H0.
      + subst.
        apply IHl2 in H0.
        destruct H0 as [H0 H1].
        apply remove_In in H0.
        contradiction.
      + apply IHl2 in H0.
        destruct H0 as [H0 H1].
        apply In_remove_other in H0.
        split; intuition.
        congruence.
  - induction l2; intros; try intuition.
    simpl in *.
    destruct (eqDecide a x) as [H3 | H3]; try intuition.
    apply IHl2.
    split.
    * apply In_remove_other. congruence. assumption.
    * assumption.
Qed.

Global Instance listMinus : Minus.
idtac.
simple refine {|
    minus := @removeList
  |}.
cbn.
unfold Setminus.
induction t; intro H0; apply Extensionality_Ensembles; simpl.
- split; intros; intuition.
- split.
  * intros x H'. destruct (eqDecide x a) as [H1 | H1].
    + split;
      subst;
      apply In_removeList in H';
      destruct H' as [H2 H3];
      apply remove_In in H2;
      contradiction.
    + split.
      -- apply In_removeList in H'; destruct H' as [H2 H3].
         apply In_remove_other in H2; assumption.
      -- intuition.
         apply In_removeList in H'; destruct H'.
         contradiction.
  * intros x H'. apply In_removeList.
    destruct (eqDecide a x).
    + subst. intuition.
    + destruct H' as [H1 H2]. split.
      -- apply In_remove_other; firstorder.
      -- firstorder.
Defined.       
    
Lemma nothingInEmpty {A} : forall (s : list A), 
    ⟦ s ⟧ = Empty_set A -> (forall a, ~In a s).
Proof.  
  intros. simpl in *.
  assert (In a s = (fun a => In a s) a) by reflexivity.
  unfold not. rewrite H in H0.
  rewrite H0.
  contradiction.
Qed.

Lemma nothingInNil {A} : forall (s : list A),
    (forall a, ~In a s) <-> s = [].
Proof.
  split; intros.
  - induction s; try reflexivity.
    assert (~In a (a :: s)) as H1 by (apply H).
    firstorder.
  - rewrite H.
    apply in_nil.
Qed.

Lemma denotationEmpty {A} : forall (s : list A),
    ⟦ s ⟧ = Empty_set A <-> s = [].
Proof.
  split; intros.
  - apply nothingInNil. apply nothingInEmpty. assumption.
  - subst. simpl.
    apply Extensionality_Ensembles.
    firstorder.
Qed.
    
Global Instance listIncSearch : IncSearch.
idtac.
simple refine {|
  incSearch := (fun (A: Type) `{eqDec A} (s' s : Space A) => search (minus s' s))
       |};
  destruct s'; intros;
    assert (s = []) as H' by (apply denotationEmpty; assumption);
    subst; simpl in *;
    try intuition; try (inversion H0; auto).
Defined.

Theorem incSearchEquiv {A} `{eqDec A} : forall s s',
    ⟦ s ⟧ = Empty_set A -> search s' = incSearch s' s.
Proof.
  intros.
  assert (s = []) by (apply denotationEmpty; assumption).
  subst.
  destruct s'; reflexivity.
Qed.

Global Instance listBindSearch : BindSearch.
idtac.
simple refine {|
  bindSearch :=
    (fun (A B : Type) `{eqDec A} (s' s : Space A) (f : A -> Space B) =>
       search (bind (minus s' s) f))
|}.
- intros. apply searchSolution. apply H0.
- intros. apply searchUninhabited. apply H0.
Defined.
