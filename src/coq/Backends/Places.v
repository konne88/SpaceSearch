Require Import ListEx.
Require Import EnsemblesEx.
Require Import SpaceSearch.
Require Import ListSpaceSearch.
Require Import Basics.
Require Import FunctionalExtensionality.

Open Scope program_scope.

Parameter Future : Type -> Type. 
Parameter force : forall {A}, Future A -> A.
Extract Constant force => "(lambda (f) (f))".

Definition map `{S:SpaceSearch} {A B} (f:A->B) s := bind s (single ∘ f).

Lemma listMapEqMap {A B l} {f:A->B} : @map listSpaceSearch A B f l = List.map f l.
  induction l.
  - reflexivity.
  - simpl in *.
    congruence.
Qed.

Class Runnable := {
  runnable : Type -> Type -> Type; 
  denoteRunnable {A B} :> Denotation (runnable A B) (A -> B);
}.

Class ParallelSearch `{SpaceSearch} `{Runnable} := {
  parallelSearch {A B} : runnable A B -> Space A -> list B;

  parallelSearchResult {A B r} {s:Space A} {b:B} :
    List.In b (parallelSearch r s) -> In ⟦ map ⟦ r ⟧ s ⟧ b;

  parallelSearchEmpty {A B r} {s:Space A} : 
    parallelSearch r s = [] -> ⟦ map ⟦ r ⟧ s ⟧ = Empty_set B
}.

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

  Definition parallelSearchPlaces (w:Worker Task Result) (ts:list Task) : list Result :=
    let p := placePool tt
    in  force <$> (enqueueTask p w <$> ts).

End ParallelSearchPlaces.

Instance parallelSearchPlaces' : @ParallelSearch listSpaceSearch runnableWorker.
  refine {|
    parallelSearch := parallelSearchPlaces
  |}.
Proof.
  - intros A B r s b h.
    rewrite listMapEqMap.
    unfold parallelSearchPlaces in h.
    apply in_map_iff in h. 
    destruct h as [f [? h]].
    subst.
    apply in_map_iff in h.
    destruct h as [a [? h]].
    subst.
    rewrite enqueueTaskOk.
    apply in_map.
    assumption.
  - intros A B r s h.
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
Defined.

Extract Constant placePool => "place-pool".
Extract Constant enqueueTask => "enqueue-task".
Extract Constant enqueueTask => "enqueue-task".

Parameter bgpvCore : Worker nat bool.
Axiom denoteBgpvCoreOk : ⟦ bgpvCore ⟧ = (fun n => true).
