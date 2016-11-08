Require Import Arith.

Class eqDec A := {
  eqDecide : forall (a a':A), {a=a'} + {a<>a'}
}.

Notation "a =? b" := (eqDecide a b).

Global Instance eqDecNat : eqDec nat.
  constructor. decide equality.
Defined.

Global Instance eqDecProd {A B} `{eqDec A} `{eqDec B} : eqDec (A * B).
  constructor; repeat decide equality; apply eqDecide.
Defined.
