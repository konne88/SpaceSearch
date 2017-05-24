Require Import EnsemblesEx.
Require Import Denotation.
Require Import Basics.
Require Import BasicTactics.

Export EnsemblesEx.
Export Denotation.

Open Scope program_scope.

Class Basic := {
  Space : Type -> Type;
  denotationSpace {A} :> Denotation (Space A) (Ensemble A);

  empty {A} : Space A;
  single {A} : A -> Space A;
  union {A} : Space A -> Space A -> Space A;
  bind {A B} : Space A -> (A -> Space B) -> Space B;
  
  denoteEmptyOk {A} : ⟦ empty ⟧ = Empty_set A;
  denoteSingleOk {A a} : ⟦ single a ⟧ = Singleton A a;
  denoteUnionOk {A s t} : ⟦ union s t ⟧ = Union A ⟦ s ⟧ ⟦ t ⟧;
  denoteBindOk {A B s f} : ⟦ bind s f ⟧ = BigUnion A B ⟦ s ⟧ (fun a => ⟦ f a ⟧);
}.

Definition map `{S:Basic} {A B} (f:A->B) s := bind s (single ∘ f).

Definition guard `{Basic}{A} (p : A -> bool) (a : A) : Space A :=
  if p a then single a else empty.

Lemma denoteGuardOk : forall `{Basic} A (p : A -> bool) (a : A),
    denote (guard p a) = if p a then denote (single a) else denote empty.
Proof.
  unfold guard.
  intros.
  break_if; auto.
Qed.

