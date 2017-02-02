Require Import Ensembles.
Export Ensembles.

Arguments In {_} / _ _.
Arguments Same_set / {_} _ _.
Arguments Included / {_} _ _.

Inductive BigUnion A B (s:Ensemble A) (f:A -> Ensemble B) : Ensemble B :=
| bigUnion a b : In s a -> In (f a) b -> In (BigUnion A B s f) b.

Lemma singletonIsEqual {A a} : Singleton A a = (fun a' => a = a').
  apply Extensionality_Ensembles.
  simpl.
  split; intros ? []; constructor.
Qed.

Lemma unionIsOr {A s t} : Union A s t = (fun a => s a \/ t a).
  apply Extensionality_Ensembles.
  simpl.
  split; intros ? []; intros; auto.
  - left; auto.
  - right; auto.
Qed.

Lemma emptyIsFalse {A} : Empty_set A = (fun _ => False).
  apply Extensionality_Ensembles.
  simpl.
  split; intros ? [].
Qed.

Lemma fullIsTrue {A} : Full_set A = (fun _ => True).
  apply Extensionality_Ensembles.
  simpl.
  split; intros ? []; constructor.
Qed.

Lemma fullForAll {A} {s : Ensemble A} : s = Full_set A <-> (forall a : A, s a).
  constructor.
  - intros Hfull a. rewrite Hfull. constructor.
  - intros Ha. apply Extensionality_Ensembles.
    simpl. constructor.
    + intros a _. constructor.
    + intros a _. firstorder.
Qed.

Lemma bigUnionIsExists {A B s f} : BigUnion A B s f = (fun b => exists a, s a /\ f a b).
  apply Extensionality_Ensembles.
  simpl.
  split.
  - intros ? [].
    firstorder.
  - intros ? [? [? ?]].
    econstructor; eauto.
Qed.

Lemma Extensionality_Ensembles' {A} {s t:Ensemble A} : (forall a, s a <-> t a) -> s = t.
  intro h.
  apply Extensionality_Ensembles.
  firstorder.
Qed.

