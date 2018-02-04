(**************************************)
(**************************************)
(****                              ****)
(****   Local closure predicates   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import Coq.Lists.List.
Require Import Main.SystemF.OpenClose.
Require Import Main.SystemF.Syntax.
Require Import Main.Tactics.

Inductive tLocallyClosed : type -> Prop :=
| tlcFreeVar :
  forall a,
  tLocallyClosed (tFreeVar a)
| tlcArrow :
  forall t1 t2,
  tLocallyClosed t1 ->
  tLocallyClosed t2 ->
  tLocallyClosed (tArrow t1 t2)
| tlcForAll :
  forall l t,
  (forall a, ~ In a l -> tLocallyClosed (taOpen t (tFreeVar a) 0)) ->
  tLocallyClosed (tForAll t).

Hint Constructors tLocallyClosed.

Definition tBody t :=
  exists l,
  forall a,
  ~ In a l ->
  tLocallyClosed (taOpen t (tFreeVar a) 0).

Theorem tForAllLocallyClosedBody :
  forall t,
  tLocallyClosed (tForAll t) <-> tBody t.
Proof.
  unfold tBody. split; eMagic; clean. invert H. eMagic.
Qed.

Hint Resolve tForAllLocallyClosedBody.
Hint Resolve <- tForAllLocallyClosedBody.

Inductive eLocallyClosed : term -> Prop :=
| elcFreeVar :
  forall x,
  eLocallyClosed (eFreeVar x)
| elcAbs :
  forall e l t,
  tLocallyClosed t ->
  (forall x, ~ In x l -> eLocallyClosed (exOpen e (eFreeVar x) 0)) ->
  eLocallyClosed (eAbs t e)
| elcApp :
  forall e1 e2,
  eLocallyClosed e1 ->
  eLocallyClosed e2 ->
  eLocallyClosed (eApp e1 e2)
| elcTAbs :
  forall e,
  eLocallyClosed e ->
  eLocallyClosed (eTAbs e)
| elcTApp :
  forall e t,
  eLocallyClosed e ->
  tLocallyClosed t ->
  eLocallyClosed (eTApp e t).

Hint Constructors eLocallyClosed.

Definition eBody e :=
  exists l,
  forall x,
  ~ In x l ->
  eLocallyClosed (exOpen e (eFreeVar x) 0).

Theorem eForAllLocallyClosedBody :
  forall e t,
  tLocallyClosed t ->
  eLocallyClosed (eAbs t e) <-> eBody e.
Proof.
  unfold eBody. split; eMagic; clean. invert H0. eMagic.
Qed.

Hint Resolve eForAllLocallyClosedBody.
Hint Resolve <- eForAllLocallyClosedBody.
