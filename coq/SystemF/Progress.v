(**********************************)
(**********************************)
(****                          ****)
(****   The progress theorem   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Main.SystemF.Semantics.
Require Import Main.SystemF.Typing.
Require Import Main.Tactics.

Theorem progress :
  forall e1 t,
  hasType cEmpty e1 t ->
  value e1 \/ exists e2, step e1 e2.
Proof.
  clean. remember cEmpty. induction H; magic; clean; right.
  - destruct IHhasType1; destruct IHhasType2; eMagic. invert H; eMagic.
  - destruct IHhasType; eMagic. invert H; eMagic.
Qed.

Hint Resolve progress.
