Require Import Basic.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.
Axiom prop_ext : prop_extensionality.

Section Full.
  Context `{Basic}.

  Class Full A := {
    full : Space A;
    denoteFullOk : ⟦ full ⟧ = Full_set A
  }.

  Arguments full _ {_}.

  Global Instance fullEmpty : Full Datatypes.Empty_set.
    refine {| full := empty |}.
  Proof.
    apply Extensionality_Ensembles'.
    intros [].
  Defined.

  Global Instance fullUnit : Full unit.
    refine {| full := single tt |}.
  Proof.
    apply Extensionality_Ensembles'.
    intros [].
    rewrite denoteSingleOk.
    rewrite singletonIsEqual.
    rewrite fullIsTrue.
    intuition.
  Defined.
  
  Global Instance fullBool : Full bool. 
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

  Global Instance fullProd {A B} `{@Full A} `{@Full B} : @Full (A * B).
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

  Global Instance fullSigT {A B} `{Full A} 
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

  Arguments full {_ _}.

  Definition all {A B} `{Full A} (q:A -> Space B) := bind full q.

  Lemma denoteAllOk {A B} `{Full A} {f:A -> Space B} : 
    ⟦ all f ⟧ = ((fun b => exists a, ⟦ f a ⟧ b) : Ensemble B).
  Proof.
    unfold all.  
    rewrite denoteBindOk.
    rewrite denoteFullOk.
    rewrite bigUnionIsExists.
    extensionality b.
    f_equal.
    extensionality a.
    apply prop_ext.
    rewrite fullIsTrue.
    intuition.
  Qed. 
End Full.
