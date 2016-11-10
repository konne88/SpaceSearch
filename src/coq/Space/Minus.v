Require Import Basic.
Require Import Full.
Require Import EqDec.

Require Import EnsemblesEx.

Class Minus `{Basic} := {
        minus {A} `{eqDec A} : Space A -> Space A -> Space A;
 
        denoteMinusOk {A s t} `{eqDec A} : ⟦ minus s t ⟧ = Setminus A ⟦ s ⟧ ⟦ t ⟧;
}.
