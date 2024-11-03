Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Sequence.
Require Import WildCat.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Diagram.
Require Import Types.

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
    (dot_step b a r) o (dot a b r) == (iota_step a) 
    := fun a b r p => inverse (pglue ((b ; r) , p)).
End InductiveStep.

Section Sequence.
  Context {A B : Type} (R : A -> B -> Type) (a0 : A).

  (** Use a record type for a full step to avoid the interleaved sequence and [flip R]. *)
  Record zigzag_type : Type := {
    Pp : Family A; (** Stored from previous step *)
    Qp : Family B; (** Stored from previous step *)
    concatQPp : Dot (flip R) Qp Pp; (** Stored from previous step *)
  }.

  Definition Q (Z : zigzag_type) : Family B
    := family_step (flip R) (concatQPp Z).

  Definition concatPQ (Z : zigzag_type) : Dot R (Pp Z) (Q Z)
    := dot_step (flip R) (concatQPp Z).

  Definition iotaQ (Z : zigzag_type) : forall (b : B) (x : Qp Z b), Q Z b
    := iota_step (flip R) (concatQPp Z).

  Definition P (Z : zigzag_type) : Family A
    := family_step R (concatPQ Z).

  Definition concatQP (Z : zigzag_type) : Dot (flip R) (Q Z) (P Z)
    := dot_step R (concatPQ Z).

  Definition iotaP (Z : zigzag_type) : forall (a : A) (x : Pp Z a), P Z a
    := iota_step R (concatPQ Z).

  Definition concatQPQ (Z : zigzag_type)
    : forall (b : B) (a : A) (r : R a b), (compose (concatPQ Z a b r) (concatQPp Z b a r)) == (iotaQ Z b)
    := homotopy_step (flip R) (concatQPp Z).

  Definition concatPQP (Z : zigzag_type)
    : forall (a : A) (b : B) (r : R a b), (compose (concatQP Z b a r) (concatPQ Z a b r)) == (iotaP Z a)
    := homotopy_step R (concatPQ Z).

  Definition zigzag_step : zigzag_type -> zigzag_type.
  Proof.
    intro Z.
    exact (Build_zigzag_type (P Z) (Q Z) (concatQP Z)).
  Defined.

  Definition identity_zigzag_initial : zigzag_type.
  Proof.
    snrapply Build_zigzag_type.
    - exact (fun a => a0 = a). (** Define [P0 := Id a0] *)
    - exact (fun b => Empty). (** Define [Q0 := Empty] *)
    - intros b a r q; destruct q. (** Define [Q0 -> P_0] *)
  Defined.

  Definition identity_zigzag : nat -> zigzag_type
    := fun n => nat_iter n zigzag_step identity_zigzag_initial.

  Definition identity_zigzag_P_seq : A -> Sequence.
  Proof.
    intro a.
    snrapply Build_Sequence.
    - intro n; exact (P (identity_zigzag n) a).
    - intro n; exact (iotaP (identity_zigzag (S n)) a).
  Defined.

  Definition identity_zigzag_Q_seq : B -> Sequence.
  Proof.
    intro b.
    snrapply Build_Sequence.
    - intro n; exact (Q (identity_zigzag n) b).
    - intro n; exact (iotaQ (identity_zigzag (S n)) b).
  Defined.

  Definition identity_zigzag_concatPQ_seq {a : A} {b : B} (r : R a b) 
    : DiagramMap (identity_zigzag_P_seq a) (succ_seq (identity_zigzag_Q_seq b)).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact (concatPQ (identity_zigzag (S n)) a b r).
    - intros n m g x.
      destruct g.
      transitivity (concatPQ (identity_zigzag (S (S n))) a b r (concatQP (identity_zigzag (S n)) b a r (concatPQ (identity_zigzag (S n)) a b r x))).
      + symmetry.
        exact (concatQPQ (identity_zigzag (S (S n))) b a r _).
      + apply ap.
        exact (concatPQP (identity_zigzag (S n)) a b r _).
  Defined.

  Definition identity_zigzag_concatQP_seq {a : A} {b : B} (r : R a b) 
    : DiagramMap (identity_zigzag_Q_seq b) (identity_zigzag_P_seq a).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact (concatQP (identity_zigzag n) b a r).
    - intros n m g x.
      destruct g.
      transitivity (concatQP (identity_zigzag (S n)) b a r (concatPQ (identity_zigzag (S n)) a b r (concatQP (identity_zigzag n) b a r x))).
      + symmetry.
        exact (concatPQP (identity_zigzag (S n)) a b r _).
      + apply ap.
        exact (concatQPQ (identity_zigzag (S n)) b a r _).
  Defined.

End Sequence.

Section Colimit.
  Context {A B : Type} (R : A -> B -> Type) (a0 : A).

Definition identity_zigzag_Pinf (a : A) : Type := 
  Colimit (identity_zigzag_P_seq R a0 a).

Definition identity_zigzag_Qinf (b : B) : Type :=
  Colimit (identity_zigzag_Q_seq R a0 b).

  Context {a : A} {b : B} (r : R a b) `{Funext}.

Definition identity_zigzag_concatQPinf
  : (identity_zigzag_Qinf b) -> (identity_zigzag_Pinf a)
  := functor_colimit (identity_zigzag_concatQP_seq R a0 r) _ _.

Definition identity_zigzag_concatPQinf 
  : (identity_zigzag_Pinf a) -> (identity_zigzag_Qinf b)
  := (colim_succ_seq_to_colim_seq _) o (functor_colimit (identity_zigzag_concatPQ_seq R a0 r) _ _ ).

End Colimit.
