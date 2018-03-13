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
  intros.
  remember cEmpty as c in H.
  induction H; magic; clean.
  - right. destruct IHhasType2; destruct IHhasType1; clean; eauto.
    + inversion H2; magic.
      exists (exOpen e e2 0).
      magic.
  - right. destruct IHhasType; clean; eauto.
    + inversion H; clean; magic.
      exists (eaOpen e0 t2 0).
      magic.
Qed.

Hint Resolve progress.
