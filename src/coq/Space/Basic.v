Require Import EnsemblesEx.
Require Import Denotation.
Require Import Basics.

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
