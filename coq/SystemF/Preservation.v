(**************************************)
(**************************************)
(****                              ****)
(****   The preservation theorem   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import Main.SystemF.Semantics.
Require Import Main.SystemF.Typing.
Require Import Main.Tactics.

Theorem preservation :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  step e1 e2 ->
  hasType cEmpty e2 t.
Proof.
  clean. gen e2. remember cEmpty. induction H; magic; clean.
  - admit.
  - admit.
Admitted.

Hint Resolve preservation.
