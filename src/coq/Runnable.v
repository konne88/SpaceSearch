Require Import Denotation.

Class Runnable := {
  runnable : Type -> Type -> Type; 
  denoteRunnable {A B} :> Denotation (runnable A B) (A -> B);
}.
