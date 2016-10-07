Require Import Basic.
Require Import Native.
Require Import Basics.
Require Import Distributed.
Require Import FunctionalExtensionality.

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

Parameter Pool : Type.
Parameter placePool : unit -> Pool.

Section ParallelSearchPlaces.
  Variable Task Result : Type.

  Parameter enqueueTask : Pool -> Worker Task Result -> Task -> Future Result.
  Axiom enqueueTaskOk : forall p w t, force (enqueueTask p w t) = ⟦ w ⟧ t.

  Definition parallelSearchPlaces (ts:list Task) (w:Worker Task Result) : list Result :=
    let p := placePool tt
    in  force <$> (enqueueTask p w <$> ts).

End ParallelSearchPlaces.

Instance parallelSearchPlaces' : @Distributed.Search _ runnableWorker.
  refine {|
    Distributed.search := parallelSearchPlaces
  |}.
Proof.
  intros A B r s b.
  constructor; intro h.
  - (* rewrite listMapEqMap.
    unfold parallelSearchPlaces in h.
    apply in_map_iff in h. 
    destruct h as [f [? h]].
    subst.
    apply in_map_iff in h.
    destruct h as [a [? h]].
    subst.
    rewrite enqueueTaskOk.
    apply in_map.
    assumption. *)
    admit.
  - admit. 
(*
    apply Extensionality_Ensembles'; intros b.
    rewrite listMapEqMap.
    constructor; [|intuition].
    intros h'.
    exfalso.
    enough (List.In b (parallelSearchPlaces A B r s)) as h''. {
      eapply in_nil.
      rewrite h in h''.
      apply h''.
    }
    clear h; rename h' into h.
    cbn in h.
    apply in_map_iff in h. 
    destruct h as [a [? h]].
    subst.
    unfold parallelSearchPlaces.
    generalize (placePool tt); intros p.
    rewrite map_map.
    rewrite in_map_iff.
    exists a.
    rewrite enqueueTaskOk.
    intuition.
*)
Admitted.

Extract Constant placePool => "place-pool".
Extract Constant enqueueTask => "enqueue-task".
Extract Constant enqueueTask => "enqueue-task".

Parameter bgpvCore : Worker nat bool.
Axiom denoteBgpvCoreOk : ⟦ bgpvCore ⟧ = (fun n => true).
