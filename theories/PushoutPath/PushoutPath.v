Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Sequence.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Diagram.
Require Import Graph.
Require Import Types.
Require Import PushoutPath.Interleaving.

(** * Work towards characterizing the path types in a pushout of a span [R : A -> B -> Type]. The goal here is to work in half-steps, so that each construction only happens once. [C] will be used to denote a type that might be [A] or [B].  We think of a term of [Family C] as being the family [fun c => a0 squiggle_t c]. *)
Definition Family (C : Type) := C -> Type.

(** Here [P a] should be thought of as [a_0 squiggle_t a] and [Q b] as [a_0 squiggle_{t+1} b].  This describes the type of the "dot" operation [- ._t -]. This will also be used with [A] and [B] swapped and [R] flipped. *)
Definition Dot {A B : Type} (R : A -> B -> Type) (P : Family A) (Q : Family B)
  := forall (a : A) (b : B) (r : R a b) (p : P a), Q b.

Section InductiveStep.

  (** Given two families [P] and [Q] and a dot map from [P] to [Q], we define one more family [P'], a stage map from [Q] to [P'] (relative to the flipped relation), and a fiberwise map iota from [P] to [P']. Note that [flip R] has type [B -> A -> Type]. *)

  Context {A B : Type} (R : A -> B -> Type).
  Context {P : Family A} {Q : Family B} (dot : Dot R P Q).

  (** We define the new type family as the pushout. *)
  Definition family_step : Family A.
  Proof.
    intro a.
    snrapply (@Pushout ({b : B & R a b} * P a) (P a) {b : B & (R a b * Q b)}).
    - exact snd.
    - intros [[b r] p].
      exact (b; (r, dot a b r p)).
  Defined.

  (** We define the next "dot" map as [pushr]. *)
  Definition dot_step : Dot (flip R) Q family_step
:= fun b a r q => pushr (b; (r, q)).

  (** We define iota as [pushl]. *)
  Definition iota_step : forall a, P a -> family_step a
    := fun a p => pushl p.

  (** We define the homotopy showing that the composition of the two dot maps is iota. *)
  Definition homotopy_step : forall (a : A) (b : B) (r : R a b), 
    (iota_step a) == (dot_step b a r) o (dot a b r) 
    := fun a b r p => (pglue ((b ; r) , p)).
End InductiveStep.
