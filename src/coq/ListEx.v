Require Import List BasicTactics EqDec.
Import ListNotations.

Export List.
Export ListNotations.

Notation "f <$> l" := (map f l) (at level 35).

Lemma concatIn {A} {a:A} l {L} : In a l -> In l L -> In a (concat L).
  induction L as [|l' L']; simpl; intros.
  + contradiction.
  + apply in_or_app.
    simpl in *.
    intuition.
    subst.
    intuition.
Qed.

Lemma concat_app {A} {l l':list (list A)} : concat (l ++ l') = concat l ++ concat l'.
  induction l; simpl.
  - reflexivity.
  - rewrite <- app_assoc.
    congruence.
Defined.

Definition elem {A} `{eqDec A} (a:A) : list A -> bool :=
  existsb (fun a' => if a =? a' then true else false).

Lemma elem_In :
  forall A `{eqDec A} a l,
    elem a l = true <-> In a l.
Proof.
  unfold elem.
  intros A H a l.
  rewrite existsb_exists.
  split.
  - intros (x & Hin & ?).
    break_if; congruence.
  - intros Hin. exists a.
    break_if; [auto | congruence].
Qed.

Fixpoint distinct {A} `{eqDec A} (l:list A) : bool :=
  match l with
  | a :: l => andb (negb (elem a l)) (distinct l)
  | [] => true
  end.

Lemma distinct_sound :
  forall A `{eqDec A} (l:list A),
    distinct l = true -> NoDup l.
Proof.
  induction l; simpl; intros.
  - constructor.
  - do_bool.
    constructor; auto.
    rewrite <- elem_In with (H := H).
    congruence.
Qed.

Lemma distinct_complete :
  forall A `{eqDec A} (l:list A),
    NoDup l -> distinct l = true.
Proof.
  induction 1; simpl.
  - auto.
  - do_bool.
    split; auto.
    rewrite <- elem_In with (H := H) in H0.
    destruct (elem x l); simpl; congruence.
Qed.

Lemma distinct_iff_NoDup :
  forall A `{eqDec A} (l:list A),
    distinct l = true <-> NoDup l.
Proof.
  intuition eauto using distinct_sound, distinct_complete.
Qed.

Lemma map_inj : forall A B (f : A -> B),
    (forall x y, f x = f y -> x = y) ->
    forall l1 l2, map f l1 = map f l2 -> l1 = l2.
Proof.
  induction l1; destruct l2; simpl; intros; auto; try discriminate.
  invc H0.
  f_equal; auto.
Qed.
