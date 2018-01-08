(**************************************************************)
(**************************************************************)
(****                                                      ****)
(****   Typing rules of the simply-typed lambda calculus   ****)
(****                                                      ****)
(**************************************************************)
(**************************************************************)

Require Import Coq.Strings.String.
Require Import Main.Stlc.Syntax.

Inductive context :=
| cEmpty : context
| cExtend : context -> string -> type -> context.

Fixpoint lookupVar c1 x1 :=
  match c1 with
  | cEmpty => None
  | cExtend c2 x2 t =>
    if string_dec x1 x2 then Some t else lookupVar c2 x1
  end.

Inductive hasType : context -> term -> type -> Prop :=
| htUnit :
  forall c,
  hasType c eUnit tUnit
| htVar :
  forall x t c,
  lookupVar c x = Some t ->
  hasType c (eVar x) t
| htAbs :
  forall e x t1 t2 c,
  hasType (cExtend c x t1) e t2 ->
  hasType c (eAbs x t1 e) (tArrow t1 t2)
| htApp :
  forall e1 e2 t1 t2 c,
  hasType c e1 t1 ->
  hasType c e2 (tArrow t1 t2) ->
  hasType c (eApp e2 e1) t2.

Hint Constructors hasType.