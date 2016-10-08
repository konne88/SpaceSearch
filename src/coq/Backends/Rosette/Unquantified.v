Require Import Basic.
Require Import Full.
Require Import Integer.
Require Import Precise.

Export Basic.
Export Full.
Export Integer.
Export Precise.

Parameter Symbolic : Type -> Type.
Parameter symbolicEmpty : forall {A}, Symbolic A.
Parameter symbolicSingle : forall {A}, A -> Symbolic A.
Parameter symbolicUnion : forall {A}, Symbolic A -> Symbolic A -> Symbolic A. 
Parameter symbolicBind : forall {A B},  Symbolic A -> (A -> Symbolic B) -> Symbolic B.
Parameter symbolicSearch : forall {A}, Symbolic A -> Precise.Result A.

Extract Constant Symbolic "a"   => "__".
Extract Constant symbolicEmpty  => "(lambda  (_) (assert false))".
Extract Constant symbolicSingle => "(lambdas (a _) a)".
Extract Constant symbolicUnion  => "(lambdas (s t v) (define-symbolic* b boolean?) (if b (s v) (t v)))".
Extract Constant symbolicBind   => "(lambdas (s f v) (@ f (s v) v))".
Extract Constant symbolicSearch    => "(lambda  (e) (solve/evaluate/concretize e))".

Axiom denoteSymbolic : forall {A}, Symbolic A -> Ensemble A.

Global Instance denotationSymbolic {A} : Denotation (Symbolic A) (Ensemble A) := {| 
  denote := denoteSymbolic
|}.

Axiom denoteSymbolicEmptyOk : forall A, ⟦ symbolicEmpty ⟧ = Empty_set A.
Axiom denoteSymbolicSingleOk : forall A a, ⟦ symbolicSingle a ⟧ = Singleton A a.
Axiom denoteSymbolicUnionOk : forall A s t, ⟦ symbolicUnion s t ⟧ = Union A ⟦ s ⟧ ⟦ t ⟧.
Axiom denoteSymbolicBindOk : forall A B s f, ⟦ symbolicBind s f ⟧ = BigUnion A B ⟦ s ⟧ (fun a => ⟦ f a ⟧).
Axiom searchSymbolicResult : forall A s (a:A), symbolicSearch s = solution a -> In ⟦ s ⟧ a.
Axiom searchSymbolicEmpty : forall A s, symbolicSearch s = uninhabited -> ⟦ s ⟧ = Empty_set A.

Global Instance rosetteBasic : Basic := {|
  Space := Symbolic;
  empty := @symbolicEmpty;
  single := @symbolicSingle;
  union := @symbolicUnion;
  bind := @symbolicBind;
|}.
Proof.
  - apply denoteSymbolicEmptyOk.
  - apply denoteSymbolicSingleOk.
  - apply denoteSymbolicUnionOk.
  - apply denoteSymbolicBindOk.
Defined.

Global Instance rosetteSearch : Precise.Search := {|
  Precise.search := @symbolicSearch
|}.
Proof.
  - apply searchSymbolicResult.
  - apply searchSymbolicEmpty.
Defined.
