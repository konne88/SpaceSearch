Require Import EnsemblesEx.
Require Import SpaceSearch.

Section Full.
  Context `{SpaceSearch}.

  Class Full A := {
    full : Space A;
    denoteFullOk : ⟦ full ⟧ = Full_set A
  }.

  Arguments full _ {_}.

  Instance fullEmpty : Full Datatypes.Empty_set.
    refine {| full := empty |}.
  Proof.
    apply Extensionality_Ensembles'.
    intros [].
  Defined.

  Instance fullUnit : Full unit.
    refine {| full := single tt |}.
  Proof.
    apply Extensionality_Ensembles'.
    intros [].
    rewrite denoteSingleOk.
    rewrite singletonIsEqual.
    rewrite fullIsTrue.
    intuition.
  Defined.
  
  Instance fullBool : Full bool. 
    refine {|
      full := union (single true) (single false)
    |}.
  Proof.
    apply Extensionality_Ensembles'.
    rewrite denoteUnionOk.
    rewrite unionIsOr.
    repeat rewrite denoteSingleOk.
    repeat rewrite singletonIsEqual.
    repeat rewrite fullIsTrue.
    intros []; firstorder.
  Defined.

  Instance fullProd {A B} `{@Full A} `{@Full B} : @Full (A * B).
    refine {|
      full := bind (full A) (fun a => 
              bind (full B) (fun b =>
              single (a, b)))
    |}.
  Proof.
    apply Extensionality_Ensembles'.
    intros [a b].
    rewrite fullIsTrue.
    intuition.
    rewrite denoteBindOk.
    econstructor; simpl. {
      rewrite denoteFullOk.
      constructor.
    }
    rewrite denoteBindOk.
    econstructor; simpl. {
      rewrite denoteFullOk.
      constructor.
    }
    rewrite denoteSingleOk.
    constructor.
  Defined.

  Instance fullSigT {A B} `{Full A} 
                          `{forall a:A, Full (B a)} : 
                            Full {a : A & B a}.
    refine {|
      full := bind (full A) (fun a => 
              bind (full (B a)) (fun b =>
              single (existT _ a b)))
    |}.
  Proof.
    apply Extensionality_Ensembles'.
    intros [a b].
    rewrite fullIsTrue.
    intuition.
    rewrite denoteBindOk.
    econstructor; simpl. {
      rewrite denoteFullOk.
      constructor.
    }
    rewrite denoteBindOk.
    econstructor; simpl. {
      rewrite denoteFullOk.
      constructor.
    }
    rewrite denoteSingleOk.
    constructor.
  Defined.
End Full.

Arguments full {_ _ _}.

