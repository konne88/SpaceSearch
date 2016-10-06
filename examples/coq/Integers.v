Require Import SpaceSearch.
Require Import Full.
Require Import Rosette.
Require Import ListEx.
Require Import Integers.

Definition solveAddTrans : list (Int * Int * Int * Int * Int) :=
  search (
    bind full (fun x:Int =>
    bind full (fun y:Int => 
    bind full (fun z:Int => 
      let a := plus (plus x y) z in
      let b := plus x (plus y z) in
        if equal a b then empty else single (x,y,z,a,b))))).

Extraction Language Scheme.

Extraction "integers" solveAddTrans.
