Require Import List.
Require Import EnsemblesEx.
Require Import Denotation.
Import ListNotations.
Export Denotation.

Class SpaceSearch := {
  Space : Type -> Type;
  empty {A} : Space A;
  single {A} : A -> Space A;
  union {A} : Space A -> Space A -> Space A;
  bind {A B} : Space A -> (A -> Space B) -> Space B;
  search {A} : Space A -> list A;

  denotationSpace {A} :> Denotation (Space A) (Ensemble A);

  denoteEmptyOk {A} : ⟦ empty ⟧ = Empty_set A;
  denoteSingleOk {A a} : ⟦ single a ⟧ = Singleton A a;
  denoteUnionOk {A s t} : ⟦ union s t ⟧ = Union A ⟦ s ⟧ ⟦ t ⟧;
  denoteBindOk {A B s f} : ⟦ bind s f ⟧ = BigUnion A B ⟦ s ⟧ (fun a => ⟦ f a ⟧);

  searchResult {A s} {a:A} : List.In a (search s) -> In ⟦ s ⟧ a;
  searchEmpty {A s} : search s = [] -> ⟦ s ⟧ = Empty_set A
}.
