Require Import Basic.
Require Import Minus.
Require Import EqDec.
Require Import Precise.

Class BindSearch `{Basic} `{Minus} := {
  bindSearch {A B} `{eqDec A} : Space A -> Space A -> (A -> Space B) -> Result B;

  bindSearchSolution {A B s' s f} {b : B} `{eqDec A} :
    ⟦ bind s f ⟧ = Empty_set B -> bindSearch s' s f = solution b -> In ⟦ bind (minus s' s) f ⟧ b;

  bindSearchUninhabited {A B s' s f} `{eqDec A} :
    ⟦ bind s f ⟧ = Empty_set B -> bindSearch s' s f = uninhabited -> ⟦ bind (minus s' s) f ⟧ = Empty_set B                                                                                   
}.