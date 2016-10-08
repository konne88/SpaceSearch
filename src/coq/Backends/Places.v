Require Import Basic.
Require Import Native.
Require Import Basics.
Require Import Distributed.
Require Import FunctionalExtensionality.

Export Distributed.

Open Scope program_scope.

Parameter Future : Type -> Type. 
Parameter force : forall {A}, Future A -> A.
Extract Constant force => "(lambda (f) (f))".

Parameter Worker : Type -> Type -> Type.
Parameter denoteWorker : forall {A B}, Worker A B -> A -> B.

Instance denotationWorker {A B} : Denotation (Worker A B) (A -> B) := {|
  denote := denoteWorker
|}.

Instance runnableWorker : Runnable := {|
  runnable := Worker
|}.

Section ParallelSearchPlaces.
  Variable Task Result : Type.

  Parameter createPool : unit -> Worker Task Result -> Task -> Future Result.
  Axiom createPoolOk : forall w t, force (createPool tt w t) = ⟦ w ⟧ t.

  Definition parallelSearchPlaces (ts:list Task) (w:Worker Task Result) : list Result :=
    let enqueueTask := createPool tt
    in  force <$> (enqueueTask w <$> ts).

End ParallelSearchPlaces.

Instance parallelSearchPlaces' : @Search listSpace runnableWorker.
  refine {|
    search := parallelSearchPlaces
  |}.
Proof.
  intros A B r s b.
  constructor; intro h.
  - rewrite listMapEqMap.
    unfold parallelSearchPlaces in h.
    rewrite map_map in h.
    apply in_map_iff in h. 
    destruct h as [f [? h]].
    subst.
    rewrite createPoolOk.
    apply in_map.
    assumption.
  - rewrite listMapEqMap in h.
    unfold parallelSearchPlaces.
    rewrite map_map.
    simpl in *.
    match goal with
    | _ : In _ (?A <$> s) |- In _ (?B <$> s) => 
      enough (B = A) by congruence
    end. 
    extensionality x.
    apply createPoolOk.
Qed.

Extract Constant createPool => "(lambda (_) (place-pool))".

