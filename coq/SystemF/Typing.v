(**************************)
(**************************)
(****                  ****)
(****   Typing rules   ****)
(****                  ****)
(**************************)
(**************************)

Require Import Coq.Lists.List.
Require Import Main.SystemF.Name.
Require Import Main.SystemF.OpenClose.
Require Import Main.SystemF.Syntax.

Import Name.

Inductive context :=
| cEmpty : context
| cTExtend : context -> eName -> type -> context
| cKExtend : context -> tName -> context.

Fixpoint xLookup c1 x1 :=
  match c1 with
  | cEmpty => None
  | cTExtend c2 x2 t => if eNameEq x1 x2 then Some t else xLookup c2 x1
  | cKExtend c2 _ => xLookup c2 x1
  end.

Fixpoint aLookup c1 a1 :=
  match c1 with
  | cEmpty => false
  | cTExtend c2 _ _ => aLookup c2 a1
  | cKExtend c2 a2 => if tNameEq a1 a2 then true else aLookup c2 a1
  end.

Inductive hasType : context -> term -> type -> Prop :=
| htFreeVar :
  forall c t x,
  xLookup c x = Some t ->
  hasType c (eFreeVar x) t
| htAbs :
  forall c e l t1 t2,
  (
    forall x,
    ~ In x l ->
    hasType (cTExtend c x t2) (exOpen e (eFreeVar x) 0) t1
  ) ->
  hasType c (eAbs t2 e) (tArrow t2 t1)
| htApp :
  forall c e1 e2 t1 t2,
  hasType c e1 (tArrow t2 t1) ->
  hasType c e2 t2 ->
  hasType c (eApp e1 e2) t1
| htTAbs :
  forall c e l t,
  (
    forall a,
    ~ In a l ->
    hasType (cKExtend c a) (eaOpen e (tFreeVar a) 0) t
  ) ->
  hasType c (eTAbs e) (tForAll t)
| htTApp :
  forall c e t1 t2,
  hasType c e (tForAll t1) ->
  hasType c (eTApp e t2) (taOpen t1 t2 0).

Hint Constructors hasType.
