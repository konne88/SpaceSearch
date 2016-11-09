Require Import Basic.
Require Import Minus.
Require Import EqDec.
Require Import Precise.

Class IncSearch `{Basic} `{Minus} := {
  incSearch {A B} `{eqDec A} : Space A -> Space A -> (A -> Space B) -> Result B;

  incSearchSolution {A B s' s f} {b : B} `{eqDec A} :
    ⟦ bind s f ⟧ = Empty_set B -> incSearch s' s f = solution b -> In ⟦ bind (minus s' s) f ⟧ b;

  incSearchUninhabited {A B s' s f} `{eqDec A} :
    ⟦ bind s f ⟧ = Empty_set B -> incSearch s' s f = uninhabited -> ⟦ bind (minus s' s) f ⟧ = Empty_set B                                                                                   
}.