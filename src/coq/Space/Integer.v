Require Import SpaceSearch.
Require Import Full.
Require Import List.
Import ListNotations.
Require Import EnsemblesEx.
Require Import ZArith.
Require Import Rosette.

Open Scope Z.

Class Integer `{Basic} := { 
  Int : Type;
  denotationInt :> Denotation Int Z;
  fullInt :> Full Int;

  mone : Int;
  zero : Int;
  one : Int;
  plus : Int -> Int -> Int;
  equal : Int -> Int -> bool;
  le : Int -> Int -> bool;

  denoteMoneOk : ⟦mone⟧ = -1;
  denoteZeroOk : ⟦zero⟧ = 0;
  denoteOneOk : ⟦one⟧ = 1;
  denotePlusOk n m : ⟦plus n m⟧ = ⟦n⟧ + ⟦m⟧;
  denoteEqualOk n m : equal n m = (⟦ n ⟧ =? ⟦ m ⟧);
  denoteLeOk n m : le n m = (⟦ n ⟧ <=? ⟦ m ⟧)
}.
