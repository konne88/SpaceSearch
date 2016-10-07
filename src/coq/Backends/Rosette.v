Require Import SpaceSearch.
Require Import List.
Import ListNotations.
Require Import EnsemblesEx.

Parameter Symbolic : Type -> Type.
Parameter symbolicEmpty : forall {A}, Symbolic A.
Parameter symbolicSingle : forall {A}, A -> Symbolic A.
Parameter symbolicUnion : forall {A}, Symbolic A -> Symbolic A -> Symbolic A. 
Parameter symbolicBind : forall {A B},  Symbolic A -> (A -> Symbolic B) -> Symbolic B.
Parameter symbolicSearch : forall {A}, Symbolic A -> list A.

Extract Constant Symbolic "a"   => "__".
Extract Constant symbolicEmpty  => "(lambda  (_) (assert false))".
Extract Constant symbolicSingle => "(lambdas (a _) a)".
Extract Constant symbolicUnion  => "(lambdas (s t v) (define-symbolic* b boolean?) (if b (s v) (t v)))".
Extract Constant symbolicBind   => "(lambdas (s f v) (@ f (s v) v))".
Extract Constant symbolicSearch    => "(lambda  (e) (solve/evaluate/concretize e))".

Axiom denoteSymbolic : forall {A}, Symbolic A -> Ensemble A.

Instance denotationSymbolic {A} : Denotation (Symbolic A) (Ensemble A) := {| 
  denote := denoteSymbolic
|}.

Axiom denoteSymbolicEmptyOk : forall A, ⟦ symbolicEmpty ⟧ = Empty_set A.
Axiom denoteSymbolicSingleOk : forall A a, ⟦ symbolicSingle a ⟧ = Singleton A a.
Axiom denoteSymbolicUnionOk : forall A s t, ⟦ symbolicUnion s t ⟧ = Union A ⟦ s ⟧ ⟦ t ⟧.
Axiom denoteSymbolicBindOk : forall A B s f, ⟦ symbolicBind s f ⟧ = BigUnion A B ⟦ s ⟧ (fun a => ⟦ f a ⟧).
Axiom searchSymbolicResult : forall A s (a:A), List.In a (symbolicSearch s) -> In ⟦ s ⟧ a.
Axiom searchSymbolicEmpty : forall A s, symbolicSearch s = [] -> ⟦ s ⟧ = Empty_set A.
  
Instance rosette : SpaceSearch := {|
  Space := Symbolic;
  empty := @symbolicEmpty;
  single := @symbolicSingle;
  union := @symbolicUnion;
  bind := @symbolicBind;
  search := @symbolicSearch
|}.
Proof.
  - apply denoteSymbolicEmptyOk.
  - apply denoteSymbolicSingleOk.
  - apply denoteSymbolicUnionOk.
  - apply denoteSymbolicBindOk.
  - apply searchSymbolicResult.
  - apply searchSymbolicEmpty.
Defined.





Parameter RosetteInt   : Type.
Parameter rosetteMone  : RosetteInt.
Parameter rosetteZero  : RosetteInt.
Parameter rosetteOne   : RosetteInt.
Parameter rosettePlus  : RosetteInt -> RosetteInt -> RosetteInt.
Parameter rosetteEqual : RosetteInt -> RosetteInt -> bool.
Parameter rosetteLe    : RosetteInt -> RosetteInt -> bool.

Extract Constant RosetteInt   => "__".
Extract Constant rosetteMone  => "-1".
Extract Constant rosetteZero  => "0".
Extract Constant rosetteOne   => "1".
Extract Constant rosettePlus  => "(lambdas (n m) (+ n m))".
Extract Constant rosetteEqual => "(lambdas (n m) (if (= n m) '(True) '(False)))".
Extract Constant rosetteLe    => "(lambdas (n m) (if (<= n m) '(True) '(False)))".

Parameter rosetteDenoteInt : RosetteInt -> Z.
Extract Constant rosetteDenoteInt => "number->z".

Instance rosetteDenotationInt : Denotation _ _ := {| 
  denote := rosetteDenoteInt
|}.

Axiom rosetteDenoteMoneOk : ⟦rosetteMone⟧ = -1.
Axiom rosetteDenoteZeroOk : ⟦rosetteZero⟧ = 0.
Axiom rosetteDenoteOneOk : ⟦rosetteOne⟧ = 1.
Axiom rosetteDenotePlusOk : forall n m, ⟦rosettePlus n m⟧ = ⟦n⟧ + ⟦m⟧.
Axiom rosetteDenoteEqualOk : forall n m, rosetteEqual n m = (⟦ n ⟧ =? ⟦ m ⟧).
Axiom rosetteDenoteLeOk : forall n m, rosetteLe n m = (⟦ n ⟧ <=? ⟦ m ⟧).

Global Instance rosetteInteger : Integer := {| 
  Int := RosetteInt;
  mone := rosetteMone;
  zero := rosetteZero;
  one := rosetteOne;
  plus := rosettePlus;
  equal := rosetteEqual;
  le := rosetteLe;
  denoteMoneOk := rosetteDenoteMoneOk;
  denoteZeroOk := rosetteDenoteZeroOk;
  denoteOneOk := rosetteDenoteOneOk;
  denotePlusOk := rosetteDenotePlusOk;
  denoteEqualOk := rosetteDenoteEqualOk;
  denoteLeOk := rosetteDenoteLeOk
|}.

Parameter fullInt : Space Int.
Axiom denoteFullIntOk : ⟦ fullInt ⟧ = Full_set Int.

Extract Constant fullInt => "(lambda (_) 
  (define-symbolic* n integer?)
  n)".

Global Instance fullRosetteInteger : Full Int := {|
  full := fullInt;
  denoteFullOk := denoteFullIntOk
|}.




