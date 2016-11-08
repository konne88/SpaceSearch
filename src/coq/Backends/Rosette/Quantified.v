Require Import Basic.
Require Import Full.
Require Import Integer.
Require Import Heuristic.

Export Basic.
Export Full.
Export Integer.
Export Heuristic.

Parameter Symbolic : Type -> Type.
Parameter symbolicEmpty : forall {A}, Symbolic A.
Parameter symbolicSingle : forall {A}, A -> Symbolic A.
Parameter symbolicUnion : forall {A}, Symbolic A -> Symbolic A -> Symbolic A. 
Parameter symbolicBind : forall {A B},  Symbolic A -> (A -> Symbolic B) -> Symbolic B.
Parameter symbolicSearch : forall {A}, Symbolic A -> Heuristic.Result A.

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

Global Instance rosetteSearch : Heuristic.Search := {|
  Heuristic.search := @symbolicSearch
|}.
Proof.
  - apply searchSymbolicResult.
  - apply searchSymbolicEmpty.
Defined.

Parameter RosetteInt   : Type.
Parameter rosetteMone  : RosetteInt.
Parameter rosetteZero  : RosetteInt.
Parameter rosetteOne   : RosetteInt.
Parameter rosettePlus  : RosetteInt -> RosetteInt -> RosetteInt.
Parameter rosetteMinus : RosetteInt -> RosetteInt -> RosetteInt.
Parameter rosetteEqual : RosetteInt -> RosetteInt -> bool.
Parameter rosetteLe    : RosetteInt -> RosetteInt -> bool.

Extract Constant RosetteInt   => "__".
Extract Constant rosetteMone  => "-1".
Extract Constant rosetteZero  => "0".
Extract Constant rosetteOne   => "1".
Extract Constant rosettePlus  => "(lambdas (n m) (+ n m))".
Extract Constant rosetteMinus  => "(lambdas (n m) (- n m))".
Extract Constant rosetteEqual => "(lambdas (n m) (if (= n m) '(True) '(False)))".
Extract Constant rosetteLe    => "(lambdas (n m) (if (<= n m) '(True) '(False)))".

Parameter rosetteDenoteInt : RosetteInt -> Z.
Extract Constant rosetteDenoteInt => "number->z".

Global Instance rosetteDenotationInt : Denotation _ _ := {| 
  denote := rosetteDenoteInt
|}.

Axiom rosetteDenoteMoneOk : ⟦rosetteMone⟧ = -1.
Axiom rosetteDenoteZeroOk : ⟦rosetteZero⟧ = 0.
Axiom rosetteDenoteOneOk : ⟦rosetteOne⟧ = 1.
Axiom rosetteDenotePlusOk : forall n m, ⟦rosettePlus n m⟧ = ⟦n⟧ + ⟦m⟧.
Axiom rosetteDenoteMinusOk : forall n m, ⟦rosetteMinus n m⟧ = ⟦n⟧ - ⟦m⟧.
Axiom rosetteDenoteEqualOk : forall n m, rosetteEqual n m = (⟦ n ⟧ =? ⟦ m ⟧).
Axiom rosetteDenoteLeOk : forall n m, rosetteLe n m = (⟦ n ⟧ <=? ⟦ m ⟧).

Parameter fullInt : Space RosetteInt.
Axiom denoteFullIntOk : ⟦ fullInt ⟧ = Full_set RosetteInt.
Extract Constant fullInt => "(lambda (_)
  (define-symbolic* n integer?)
  n)".

Global Instance fullRosetteInteger : @Full rosetteBasic RosetteInt := {|
  full := fullInt;
  denoteFullOk := denoteFullIntOk
|}.

Global Instance rosetteInteger : @Integer rosetteBasic := {| 
  Int := RosetteInt;
  mone := rosetteMone;
  zero := rosetteZero;
  one := rosetteOne;
  plus := rosettePlus;
  minus := rosetteMinus;
  equal := rosetteEqual;
  le := rosetteLe;
  denoteMoneOk := rosetteDenoteMoneOk;
  denoteZeroOk := rosetteDenoteZeroOk;
  denoteOneOk := rosetteDenoteOneOk;
  denotePlusOk := rosetteDenotePlusOk;
  denoteMinusOk := rosetteDenoteMinusOk;
  denoteEqualOk := rosetteDenoteEqualOk;
  denoteLeOk := rosetteDenoteLeOk
|}.

