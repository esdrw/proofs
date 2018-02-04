(***********************)
(***********************)
(****               ****)
(****   Semantics   ****)
(****               ****)
(***********************)
(***********************)

Require Import Main.SystemF.OpenClose.
Require Import Main.SystemF.Syntax.

Inductive value : term -> Prop :=
| vAbs : forall e t, value (eAbs t e)
| vTAbs : forall e, value (eTAbs e).

Hint Constructors value.

Inductive step : term -> term -> Prop :=
| sBeta :
  forall e1 e2 t,
  value e2 ->
  step (eApp (eAbs t e1) e2) (exOpen e1 e2 0)
| sApp1 :
  forall e1 e2 e3,
  step e1 e2 ->
  step (eApp e1 e3) (eApp e2 e3)
| sApp2 :
  forall e1 e2 e3,
  value e1 ->
  step e2 e3 ->
  step (eApp e1 e2) (eApp e1 e3)
| sTApp :
  forall e1 e2 t,
  step e1 e2 ->
  step (eTApp e1 t) (eTApp e2 t)
| sTBeta :
  forall e1 t,
  step (eTApp (eTAbs e1) t) (eaOpen e1 t 0).

Hint Constructors step.

Inductive stepStar : term -> term -> Prop :=
| scRefl :
  forall e,
  stepStar e e
| scStep :
  forall e1 e2 e3,
  step e1 e2 ->
  stepStar e2 e3 ->
  stepStar e1 e3.

Hint Constructors stepStar.
