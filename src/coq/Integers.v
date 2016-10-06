Require Import SpaceSearch.
Require Import Full.
Require Import List.
Import ListNotations.
Require Import EnsemblesEx.
Require Import ZArith.
Require Import Rosette.

Open Scope Z.

Class Integer := { 
  Int : Type;
  mone : Int;
  zero : Int;
  one : Int;
  plus : Int -> Int -> Int;
  equal : Int -> Int -> bool;
  le : Int -> Int -> bool;

  denotationInt :> Denotation Int Z;
  denoteMoneOk : ⟦mone⟧ = -1;
  denoteZeroOk : ⟦zero⟧ = 0;
  denoteOneOk : ⟦one⟧ = 1;
  denotePlusOk n m : ⟦plus n m⟧ = ⟦n⟧ + ⟦m⟧;
  denoteEqualOk n m : equal n m = (⟦ n ⟧ =? ⟦ m ⟧);
  denoteLeOk n m : le n m = (⟦ n ⟧ <=? ⟦ m ⟧)
}.

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
Extract Constant rosetteEqual => "(lambdas (n m) (= n m))".
Extract Constant rosetteLe    => "(lambdas (n m) (<= n m))".

Parameter rosetteDenoteInt : RosetteInt -> Z.
Extract Constant rosetteDenoteInt => "integer->z".

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
  (define-symbolic n integer?)
  n)".

Global Instance fullRosetteInteger : Full Int := {|
  full := fullInt;
  denoteFullOk := denoteFullIntOk
|}.
