(**************************)
(**************************)
(****                  ****)
(****   Substitution   ****)
(****                  ****)
(**************************)
(**************************)

Require Import Main.SystemF.Name.
Require Import Main.SystemF.Syntax.

Import Name.

Fixpoint exSub e1 x1 e2 :=
  match e1 with
  | eFreeVar x2 => if eNameEq x1 x2 then e2 else e1
  | eBoundVar _ => e1
  | eAbs t e3 => eAbs t (exSub e3 x1 e2)
  | eApp e3 e4 => eApp (exSub e3 x1 e2) (exSub e4 x1 e2)
  | eTAbs e3 => eTAbs (exSub e3 x1 e2)
  | eTApp e3 t => eTApp (exSub e3 x1 e2) t
  end.

Fixpoint taSub t1 a1 t2 :=
  match t1 with
  | tFreeVar a2 => if tNameEq a1 a2 then t2 else t1
  | tBoundVar _ => t1
  | tArrow t3 t4 => tArrow (taSub t3 a1 t2) (taSub t4 a1 t2)
  | tForAll t3 => tForAll (taSub t3 a1 t2)
  end.

Fixpoint eaSub e1 a1 t1 :=
  match e1 with
  | eFreeVar _ => e1
  | eBoundVar _ => e1
  | eAbs t2 e2 => eAbs (taSub t2 a1 t1) (eaSub e2 a1 t1)
  | eApp e2 e3 => eApp (eaSub e2 a1 t1) (eaSub e3 a1 t1)
  | eTAbs e2 => eTAbs (eaSub e2 a1 t1)
  | eTApp e2 t2 => eTApp (eaSub e2 a1 t1) (taSub t2 a1 t1)
  end.
