Require Import Basic.
Require Import Minus.
Require Import EqDec.
Require Import Precise.

Class IncSearch `{Basic} `{Minus} := {
  incSearch {A} `{eqDec A} : Space A -> Space A -> Result A;

  incSearchSolution {A s' s} {a : A} `{eqDec A} : ⟦ s ⟧ = Empty_set A -> incSearch s' s = solution a -> In ⟦ minus s' s ⟧ a;

  incSearchUninhabited {A s' s} `{eqDec A} : ⟦ s ⟧ = Empty_set A -> incSearch s' s = uninhabited -> ⟦ minus s' s ⟧ = Empty_set A
}.

                                                                                                                                
 