Require Import Basic Integer Full.

(* Include all the basic tactics as well. *)
Require Export BasicTactics.

(*** Tactics for SpaceSearch ***)

(* Add all the denotation lemmas to a rewrite database. As SpaceSearch expands,
   any new denotation lemmas should be added to the database. *)
Hint Rewrite @denoteEmptyOk @denoteSingleOk @denoteBindOk @bigUnionIsExists : space.
Hint Rewrite @denoteFullOk @denoteGuardOk : space.
Hint Rewrite @denoteZeroOk @denoteOneOk @denotePlusOk @denoteLeOk @denoteEqualOk : space.
Hint Rewrite @denoteLtOk @denoteFromZOk @denoteMinusOk @fromZInv : space.

Hint Constructors Singleton : space.

(* The constructor for Singleton is hidden behind an invocation of Ensembles.In,
   which makes [auto] reluctant to use it. The following lemma is better for
   auto. *)
Lemma In_singleton' : forall A (x : A), Singleton A x x.
Proof. exact In_singleton. Qed.
Hint Resolve In_singleton' : space.

(* See comment above. *)
Lemma Full_intro' : forall A (x : A), Full_set A x.
Proof. exact Full_intro. Qed.
Hint Resolve Full_intro' : space.

(* Break apart common artifacts from rewriting by denotation lemmas. For
   example, rewriting by bigUnionIsExists results in an existential, which we'd
   like to destruct.

   One annoying perennial issue with this tactics library is the distinction
   between Ensembles.In and the lack thereof. The issue is that some places use
   In, while others directly apply the Ensemble to the member. This is fine,
   except that automation gets confused and doesn't know that they are the same.
   Probably Ensembles.In should have been declared a notation in the first
   place, instead of a definition, but that will never change now. It would be
   nice to eventually come up with a better workaround than just always
   duplicating cases, like below.  *)
Ltac break_space :=
  repeat
    match goal with
    | [ H : Ensembles.In (fun _ => exists _, _ /\ _) _ |- _ ] => destruct H as (? & ? & ?)
    | [ H : Ensembles.In (Singleton _ _) _ |- _ ] => invc H
    | [ H : Ensembles.In (Empty_set _) _ |- _ ] => invc H
    | [ H : exists _, _ /\ _ |- _ ] => destruct H as (? & ? & ?)
    | [ H : Singleton _ _ _ |- _ ] => invc H
    | [ H : Empty_set _ _ |- _ ] => invc H
    end.

Ltac break_and :=
  repeat
    match goal with
    | [ H : _ /\ _ |- _ ] => destruct H
    end.

(* The main SpaceSearch workhorse tactic. Repeatedly rewrite by denotation
   lemmas, destruct their results, and convert booleans to Props. Finally,
   cleanup by trying a few basic Ensemble constructors. *)
Ltac space_crush :=
  intros;
  repeat
    (autorewrite with list space in *;
     break_space;
     do_bool; break_and);
  auto with space.
