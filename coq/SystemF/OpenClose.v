(******************************************)
(******************************************)
(****                                  ****)
(****   Variable opening and closing   ****)
(****                                  ****)
(******************************************)
(******************************************)

Require Import Coq.Arith.Peano_dec.
Require Import Main.SystemF.Name.
Require Import Main.SystemF.Syntax.

Import Name.

Fixpoint exOpen e1 e2 i1 :=
  match e1 with
  | eFreeVar _ => e1
  | eBoundVar i2 => if eq_nat_dec i1 i2 then e2 else e1
  | eAbs t e3 => eAbs t (exOpen e3 e2 (S i1))
  | eApp e3 e4 => eApp (exOpen e3 e2 i1) (exOpen e4 e2 i1)
  | eTAbs e3 => eTAbs (exOpen e3 e2 i1)
  | eTApp e3 t => eTApp (exOpen e3 e2 i1) t
  end.

Fixpoint taOpen t1 t2 i1 :=
  match t1 with
  | tFreeVar _ => t1
  | tBoundVar i2 => if eq_nat_dec i1 i2 then t2 else t1
  | tArrow t3 t4 => tArrow (taOpen t3 t2 i1) (taOpen t4 t2 i1)
  | tForAll t3 => tForAll (taOpen t3 t2 (S i1))
  end.

Fixpoint eaOpen e1 t1 i1 :=
  match e1 with
  | eFreeVar _ => e1
  | eBoundVar _ => e1
  | eAbs t2 e2 => eAbs (taOpen t2 t1 i1) (eaOpen e2 t1 i1)
  | eApp e2 e3 => eApp (eaOpen e2 t1 i1) (eaOpen e3 t1 i1)
  | eTAbs e2 => eTAbs (eaOpen e2 t1 (S i1))
  | eTApp e2 t2 => eTApp (eaOpen e2 t1 i1) (taOpen t2 t1 i1)
  end.

Fixpoint exClose e1 x1 i :=
  match e1 with
  | eFreeVar x2 => if eNameEq x1 x2 then eBoundVar i else e1
  | eBoundVar _ => e1
  | eAbs t e2 => eAbs t (exClose e2 x1 (S i))
  | eApp e2 e3 => eApp (exClose e2 x1 i) (exClose e3 x1 i)
  | eTAbs e2 => eTAbs (exClose e2 x1 i)
  | eTApp e2 t => eTApp (exClose e2 x1 i) t
  end.

Fixpoint taClose t1 a1 i :=
  match t1 with
  | tFreeVar a2 => if tNameEq a1 a2 then tBoundVar i else t1
  | tBoundVar _ => t1
  | tArrow t2 t3 => tArrow (taClose t2 a1 i) (taClose t3 a1 i)
  | tForAll t2 => tForAll (taClose t2 a1 (S i))
  end.

Fixpoint eaClose e1 a1 i :=
  match e1 with
  | eFreeVar _ => e1
  | eBoundVar _ => e1
  | eAbs t e2 => eAbs (taClose t a1 i) (eaClose e2 a1 i)
  | eApp e2 e3 => eApp (eaClose e2 a1 i) (eaClose e3 a1 i)
  | eTAbs e2 => eTAbs (eaClose e2 a1 (S i))
  | eTApp e2 t => eTApp (eaClose e2 a1 i) (taClose t a1 i)
  end.
