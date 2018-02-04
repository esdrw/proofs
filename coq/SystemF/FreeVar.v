(****************************)
(****************************)
(****                    ****)
(****   Free variables   ****)
(****                    ****)
(****************************)
(****************************)

Require Import Coq.Lists.List.
Require Import Main.SystemF.Syntax.

Import ListNotations.

Fixpoint exFreeVars e1 :=
  match e1 with
  | eFreeVar x => [x]
  | eBoundVar _ => []
  | eAbs _ e2 => exFreeVars e2
  | eApp e2 e3 => exFreeVars e2 ++ exFreeVars e3
  | eTAbs e2 => exFreeVars e2
  | eTApp e2 _ => exFreeVars e2
  end.

Fixpoint taFreeVars t1 :=
  match t1 with
  | tFreeVar a => [a]
  | tBoundVar _ => []
  | tArrow t2 t3 => taFreeVars t2 ++ taFreeVars t3
  | tForAll t2 => taFreeVars t2
  end.

Fixpoint eaFreeVars e1 :=
  match e1 with
  | eFreeVar x => []
  | eBoundVar _ => []
  | eAbs t e2 => taFreeVars t ++ eaFreeVars e2
  | eApp e2 e3 => eaFreeVars e2 ++ eaFreeVars e3
  | eTAbs e2 => eaFreeVars e2
  | eTApp e2 t => eaFreeVars e2 ++ taFreeVars t
  end.
