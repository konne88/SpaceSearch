Require Import List.
Require Import Basic.
Require Import Runnable.

Export Runnable.

Module Distributed.
  Class Search `{Basic} `{Runnable} := {
    search {A B} : Space A -> runnable A B -> list B;
    searchResult {A B r} {s:Space A} {b:B} :
      List.In b (search s r) <-> In ⟦ map ⟦ r ⟧ s ⟧ b
  }.
End Distributed.
