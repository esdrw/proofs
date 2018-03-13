(****************************)
(****************************)
(****                    ****)
(****   Helpful lemmas   ****)
(****                    ****)
(****************************)
(****************************)

Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import Main.SystemF.FreeVar.
Require Import Main.SystemF.LocalClosure.
Require Import Main.SystemF.Name.
Require Import Main.SystemF.OpenClose.
Require Import Main.SystemF.Syntax.
Require Import Main.Tactics.

Import ListNotations.
Import Name.

Lemma taOpenEquals :
  forall i j t1 t2 t3,
  i <> j ->
  taOpen (taOpen t1 t2 i) t3 j = taOpen t1 t2 i ->
  taOpen t1 t3 j = t1.
Proof.
  intros.
  generalize dependent i.
  generalize dependent j.
  induction t1; clean; magic; inversion H0; f_equal.
  - apply IHt1_1 with (i := i) (j := j); auto.
  - apply IHt1_2 with (i := i) (j := j); auto.
  - apply IHt1 with (i := S i) (j := S j); auto.
Qed.

Theorem taOpenLocallyClosed :
  forall i t1 t2,
  tLocallyClosed t1 ->
  taOpen t1 t2 i = t1.
Proof.
  intros.
  generalize dependent i.
  generalize dependent t2.
  induction H; magic.
  clean.
  f_equal.
  pose (H1 := tNameFresh l).
  destruct H1.
  specialize (H0 x H1).
  apply taOpenEquals with (i := 0) (j := S i) (t2 := tFreeVar x); auto.
Qed.

Theorem exCloseOpenVar :
  forall e i x,
  exFreeVars e = [] ->
  exClose (exOpen e (eFreeVar x) i) x i = e.
Proof.
  clean. gen i. induction e; magic; clean. apply app_eq_nil in H. magic.
Qed.

Hint Resolve exCloseOpenVar.

Theorem taCloseOpenVar :
  forall a t i,
  taFreeVars t = [] ->
  taClose (taOpen t (tFreeVar a) i) a i = t.
Proof.
  clean. gen i. induction t; magic; clean. apply app_eq_nil in H. magic.
Qed.

Hint Resolve taCloseOpenVar.

Theorem eaCloseOpenVar :
  forall a e i,
  eaFreeVars e = [] ->
  eaClose (eaOpen e (tFreeVar a) i) a i = e.
Proof.
  clean. gen i. induction e; magic; clean; apply app_eq_nil in H; magic.
Qed.

Hint Resolve eaCloseOpenVar.

Theorem exOpenOpenClose :
  forall e i1 i2 x1 x2,
  i1 <> i2 ->
  exOpen (exClose (exOpen e (eFreeVar x1) i1) x2 i2) (eFreeVar x2) i2 =
  exOpen (exOpen (exClose e x2 i2) (eFreeVar x2) i2) (eFreeVar x1) i1.
Proof.
  clean. gen i1 i2. induction e; magic.
Qed.

Hint Resolve exOpenOpenClose.

Theorem taOpenOpenClose :
  forall a1 a2 i1 i2 t,
  i1 <> i2 ->
  taOpen (taClose (taOpen t (tFreeVar a1) i1) a2 i2) (tFreeVar a2) i2 =
  taOpen (taOpen (taClose t a2 i2) (tFreeVar a2) i2) (tFreeVar a1) i1.
Proof.
  clean. gen i1 i2. induction t; magic.
Qed.

Hint Resolve taOpenOpenClose.

Theorem eaOpenOpenClose :
  forall a e i1 i2 x,
  eaOpen (eaClose (exOpen e (eFreeVar x) i1) a i2) (tFreeVar a) i2 =
  exOpen (eaOpen (eaClose e a i2) (tFreeVar a) i2) (eFreeVar x) i1.
Proof.
  clean. gen i1 i2. induction e; magic.
Qed.

Hint Resolve eaOpenOpenClose.

Section FreeClose.

  Local Theorem removeDistributive :
    forall {T} {eqDec} (l1 l2 : list T) x,
    remove eqDec x (l1 ++ l2) = remove eqDec x l1 ++ remove eqDec x l2.
  Proof.
    induction l1; magic.
  Qed.

  Hint Rewrite (@removeDistributive eName eNameEq).
  Hint Rewrite (@removeDistributive tName tNameEq).

  Theorem exFreeClose :
    forall e i x,
    exFreeVars (exClose e x i) = remove eNameEq x (exFreeVars e).
  Proof.
    clean. gen i. induction e; magic.
  Qed.

  Theorem taFreeClose :
    forall a i t,
    taFreeVars (taClose t a i) = remove tNameEq a (taFreeVars t).
  Proof.
    clean. gen i. induction t; magic.
  Qed.

  Theorem eaFreeClose :
    forall a e i,
    exFreeVars (eaClose e a i) = exFreeVars e.
  Proof.
    clean. gen i. induction e; magic.
  Qed.

End FreeClose.

Hint Rewrite exFreeClose.

Hint Rewrite taFreeClose.

Hint Rewrite eaFreeClose.

Theorem exFreeOpen :
  forall e i x,
  incl (exFreeVars (exOpen e (eFreeVar x) i)) (x :: exFreeVars e).
Proof.
  clean. gen i. induction e; magic. clean. apply incl_app.
  - rewrite app_comm_cons. apply incl_appl. magic.
  - apply incl_tran with (m := x :: exFreeVars e2); magic.
Qed.

Hint Resolve exFreeOpen.

Theorem taFreeOpen :
  forall a i t,
  incl (taFreeVars (taOpen t (tFreeVar a) i)) (a :: taFreeVars t).
Proof.
  clean. gen i. induction t; magic. clean. apply incl_app.
  - rewrite app_comm_cons. apply incl_appl. magic.
  - apply incl_tran with (m := a :: taFreeVars t2); magic.
Qed.

Hint Resolve taFreeOpen.

Theorem eaFreeOpen :
  forall a e i,
  incl (exFreeVars (eaOpen e (tFreeVar a) i)) (exFreeVars e).
Proof.
  clean. gen i. induction e; magic.
Qed.

Hint Resolve eaFreeOpen.

Theorem exOpenInversion :
  forall e1 e2 i x,
  ~ In x (exFreeVars e1) ->
  ~ In x (exFreeVars e2) ->
  exOpen e1 (eFreeVar x) i = exOpen e2 (eFreeVar x) i ->
  e1 = e2.
Proof.
  clean. gen e2 i. induction e1; induction e2; magic; clean.
  - destruct (PeanoNat.Nat.eq_dec i n); magic. invert H1. magic.
  - destruct (PeanoNat.Nat.eq_dec i n); magic. invert H1. magic.
  - specialize (IHe1 (S i) e2). invert H1. magic.
  - specialize (IHe1_1 i e2_1). specialize (IHe1_2 i e2_2). clean. magic.
  - specialize (IHe1 i e2). clean. magic.
  - specialize (IHe1 i e2). clean. magic.
Qed.

Hint Resolve exOpenInversion.

Theorem taOpenInversion :
  forall a i t1 t2,
  ~ In a (taFreeVars t1) ->
  ~ In a (taFreeVars t2) ->
  taOpen t1 (tFreeVar a) i = taOpen t2 (tFreeVar a) i ->
  t1 = t2.
Proof.
  clean. gen t2 i. induction t1; induction t2; magic; clean.
  - destruct (PeanoNat.Nat.eq_dec i n); magic. invert H1. magic.
  - destruct (PeanoNat.Nat.eq_dec i n); magic. invert H1. magic.
  - specialize (IHt1_1 i t2_1). specialize (IHt1_2 i t2_2). clean. magic.
  - specialize (IHt1 (S i) t2). clean. magic.
Qed.

Hint Resolve taOpenInversion.

Theorem eaOpenInversion :
  forall a e1 e2 i,
  ~ In a (eaFreeVars e1) ->
  ~ In a (eaFreeVars e2) ->
  eaOpen e1 (tFreeVar a) i = eaOpen e2 (tFreeVar a) i ->
  e1 = e2.
Proof.
  clean. gen e2 i. induction e1; induction e2; magic; clean.
  - specialize (IHe1 i e2). clean.
    f_equal. apply taOpenInversion with (a := a) (i := i); magic.
  - specialize (IHe1_1 i e2_1). specialize (IHe1_2 i e2_2). clean. magic.
  - specialize (IHe1 (S i) e2). clean. magic.
  - specialize (IHe1 i e2). clean.
    f_equal. apply taOpenInversion with (a := a) (i := i); magic.
Qed.

Hint Resolve eaOpenInversion.

Section openCloseVar.

  Local Theorem inIncl :
    forall T x (l1 l2 : list T),
    In x l1 ->
    incl l1 l2 ->
    In x l2.
  Proof.
    magic.
  Qed.

  Hint Resolve inIncl.

  Local Theorem inRemove :
    forall T (l : list T) (equiv : forall x1 x2, {x1 = x2} + {x1 <> x2}) x1 x2,
    In x1 (remove equiv x2 l) ->
    In x1 l.
  Proof.
    clean. induction l; magic.
  Qed.

  Hint Resolve inRemove.

  Theorem exOpenCloseVar :
    forall e i x,
    eLocallyClosed e ->
    exOpen (exClose e x i) (eFreeVar x) i = e.
  Proof.
    clean. gen i. induction H; magic. clean.
    f_equal.
    fact (eNameFresh (l ++ [x] ++ exFreeVars e)). clean.
    specialize (H1 x0). clean. specialize (H1 (S i)).
    rewrite exOpenOpenClose in H1; magic.
    apply exOpenInversion with (i := 0) (x := x0); magic.
    unfold not. clean.
    assert (In x0 (x :: exFreeVars (exClose e x (S i)))); eMagic.
  Qed.

  Theorem taOpenCloseVar :
    forall a t i,
    tLocallyClosed t ->
    taOpen (taClose t a i) (tFreeVar a) i = t.
  Proof.
    clean. gen i. induction H; magic. clean.
    f_equal.
    fact (tNameFresh (l ++ [a] ++ taFreeVars t)). clean.
    specialize (H0 x). clean. specialize (H0 (S i)).
    rewrite taOpenOpenClose in H0; magic.
    apply taOpenInversion with (i := 0) (a := x); magic.
    unfold not. clean.
    assert (In x (a :: taFreeVars (taClose t a (S i)))); eMagic.
  Qed.

  Hint Resolve taOpenCloseVar.

  Theorem eaOpenCloseVar :
    forall a e i,
    eLocallyClosed e ->
    eaOpen (eaClose e a i) (tFreeVar a) i = e.
  Proof.
    clean. gen i. induction H; magic. clean.
    f_equal; magic.
    fact (eNameFresh (l ++ exFreeVars e)). clean.
    specialize (H1 x). clean. specialize (H1 i).
    rewrite eaOpenOpenClose in H1; magic.
    apply exOpenInversion with (i := 0) (x := x); magic.
    unfold not. clean.
    assert (In x (exFreeVars (eaClose e a i))); eMagic.
  Qed.

End openCloseVar.

Hint Resolve exOpenCloseVar.

Hint Resolve taOpenCloseVar.

Hint Resolve eaOpenCloseVar.
