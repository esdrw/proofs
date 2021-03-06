(************************)
(************************)
(****                ****)
(****   Categories   ****)
(****                ****)
(************************)
(************************)

Require Import Main.Tactics.

Set Universe Polymorphism.

(* Metavariables for categories: C, D, E *)

Record category := newCategory {
  object : Type; (* Metavariables for objects: w, x, y, z *)
  arrow : object -> object -> Type; (* Metavariables for arrows: f, g, h *)
  compose : forall {x y z}, arrow y z -> arrow x y -> arrow x z;
  id : forall {x}, arrow x x;

  cAssoc :
    forall w x y z (f : arrow w x) (g : arrow x y) (h : arrow y z),
    compose h (compose g f) = compose (compose h g) f;
  cIdentLeft : forall x y (f : arrow x y), compose id f = f;
  cIdentRight : forall x y (f : arrow x y), compose f id = f;
}.

Hint Resolve cAssoc.
Hint Resolve cIdentLeft.
Hint Rewrite cIdentLeft.
Hint Resolve cIdentRight.
Hint Rewrite cIdentRight.

Definition opCategory (C : category) : @category.
Proof.
  refine (newCategory
    (object C)
    (fun x y => arrow C y x)
    (fun {x y z} f g => compose C g f)
    (fun {x} => id C)
    _ _ _
  ); magic.
Defined.

Definition thin (C : category) :=
  forall x y (f g : arrow C x y), f = g.

(* Morphisms *)

Definition epimorphism {C x y} (f : arrow C x y) :=
  forall z (g h : arrow C y z), compose C g f = compose C h f -> g = h.

Definition monomorphism {C x y} (f : arrow C x y) :=
  forall z (g h : arrow C z x), compose C f g = compose C f h -> g = h.

Definition isomorphism {C x y} (f : arrow C x y) :=
  exists g, compose C g f = id C /\ compose C f g = id C.

Theorem leftIdUnique :
  forall C x f,
  (forall y (g : arrow C y x), compose C f g = g) ->
  f = id C.
Proof.
  clean.
  specialize (H x (id C)).
  magic.
Qed.

Hint Resolve leftIdUnique.

Theorem rightIdUnique :
  forall C x f,
  (forall y (g : arrow C x y), compose C g f = g) ->
  f = id C.
Proof.
  clean.
  specialize (H x (id C)).
  magic.
Qed.

Hint Resolve rightIdUnique.

Theorem isoImpliesEpi :
  forall C x y f, @isomorphism C x y f -> @epimorphism C x y f.
Proof.
  unfold isomorphism.
  unfold epimorphism.
  clean.
  assert (
    compose C (compose C g f) x0 = compose C (compose C h f) x0
  ); magic.
  repeat rewrite <- cAssoc in H2.
  repeat rewrite H1 in H2.
  magic.
Qed.

Hint Resolve isoImpliesEpi.

Theorem isoImpliesMono :
  forall C x y f, @isomorphism C x y f -> @monomorphism C x y f.
Proof.
  unfold isomorphism.
  unfold monomorphism.
  clean.
  assert (
    compose C x0 (compose C f g) = compose C x0 (compose C f h)
  ); magic.
  repeat rewrite cAssoc in H2.
  repeat rewrite H in H2.
  magic.
Qed.

Hint Resolve isoImpliesMono.

Theorem opIso :
  forall C x y,
  (exists f, @isomorphism C x y f) <->
  (exists f, @isomorphism (opCategory C) x y f).
Proof.
  unfold isomorphism; split; clean; exists x1; eMagic.
Qed.

Hint Resolve opIso.

(* Objects *)

Definition initial {C} x :=
  forall y,
  exists f,
  forall (g : arrow C x y), f = g.

Definition terminal {C} x :=
  forall y,
  exists f,
  forall (g : arrow C y x), f = g.

Theorem opInitialTerminal :
  forall C x,
  @initial C x <->
  @terminal (opCategory C) x.
Proof.
  magic.
Qed.

Hint Resolve opInitialTerminal.

Theorem opTerminalInitial :
  forall C x,
  @terminal C x <->
  @initial (opCategory C) x.
Proof.
  magic.
Qed.

Hint Resolve opTerminalInitial.

Theorem initialUnique :
  forall C x y,
  initial x ->
  initial y ->
  exists f,
  @isomorphism C x y f.
Proof.
  unfold initial.
  clean.
  fact (H x). specialize (H y).
  fact (H0 x). specialize (H0 y).
  clean.
  exists x3.
  unfold isomorphism.
  exists x0.
  split; magic.
Qed.

Hint Resolve initialUnique.

Theorem terminalUnique :
  forall C x y,
  terminal x ->
  terminal y ->
  exists f,
  @isomorphism C x y f.
Proof.
  clean.
  rewrite opTerminalInitial in *.
  apply opIso.
  apply initialUnique; magic.
Qed.

Hint Resolve terminalUnique.
