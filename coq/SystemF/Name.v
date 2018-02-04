(*******************************************)
(*******************************************)
(****                                   ****)
(****   Names with decidable equality   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Coq.Lists.List.
Require Import Main.Tactics.

Import ListNotations.

Module Type NameSig.

  (* Term variables *)

  Parameter eName : Set.

  Axiom eNameEq : forall x1 x2 : eName, { x1 = x2 } + { x1 <> x2 }.

  Axiom eNameFresh : forall l : list eName, exists x, ~ In x l.

  (* Type variables *)

  Parameter tName : Set.

  Axiom tNameEq : forall x1 x2 : tName, { x1 = x2 } + { x1 <> x2 }.

  Axiom tNameFresh : forall l : list tName, exists x, ~ In x l.

End NameSig.

Module Name : NameSig.

  Definition eName := nat.

  Theorem eNameEq : forall x1 x2 : nat, { x1 = x2 } + { x1 <> x2 }.
  Proof.
    induction x1; magic.
  Qed.

  Hint Resolve eNameEq.

  Theorem eNameFresh : forall l : list nat, exists x, ~ In x l.
  Proof.
    clean.
    exists (S (fold_right max 0 l)).
    unfold not. clean.
    assert (forall n, In n l -> n <= (fold_right Nat.max 0 l)).
    - clear H. clean. induction l; magic.
      assert ((fold_right max 0 l) <= max a (fold_right max 0 l)); magic.
    - specialize (H0 (S (fold_right Nat.max 0 l))). magic.
  Qed.

  Hint Resolve eNameFresh.

  Definition tName := eName.

  Definition tNameEq := eNameEq.

  Hint Resolve tNameEq.

  Definition tNameFresh := eNameFresh.

  Hint Resolve tNameFresh.

End Name.
