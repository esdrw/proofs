(********************)
(********************)
(****            ****)
(****   Syntax   ****)
(****            ****)
(********************)
(********************)

Require Import Main.SystemF.Name.

Import Name.

Inductive term : Set :=
| eFreeVar : eName -> term
| eBoundVar : nat -> term
| eAbs : type -> term -> term
| eApp : term -> term -> term
| eTAbs : term -> term
| eTApp : term -> type -> term

with type : Set :=
| tFreeVar : tName -> type
| tBoundVar : nat -> type
| tArrow : type -> type -> type
| tForAll : type -> type.
