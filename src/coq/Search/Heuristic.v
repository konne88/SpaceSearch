Require Import Basic.

Inductive Result {A} := solution (a:A) | uninhabited | unknown.
Arguments Result _ : clear implicits.

Class Search `{Basic} := {
  search {A} : Space A -> Result A;
  searchSolution {A s} {a:A} : search s = solution a -> In ⟦ s ⟧ a;
  searchUninhabited {A s} : search s = uninhabited -> ⟦ s ⟧ = Empty_set A
}.
