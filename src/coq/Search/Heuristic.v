Require Import Basic.

Inductive Result {A} := solution (a:A) | empty | unknown.
Arguments Result _ : clear implicits.

Class Search `{Basic} := {
  search {A} : Space A -> Result A;
  searchResult {A s} {a:A} : search s = solution a -> In ⟦ s ⟧ a;
  searchEmpty {A s} : search s = empty -> ⟦ s ⟧ = Empty_set A
}.
