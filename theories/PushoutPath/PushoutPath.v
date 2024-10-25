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

(** * Work towards characterizing the path types in a pushout of a span [R : A -> B -> Type]. *)

(** The goal here is to work in half-steps, so that each construction only happens once. *)

(** [C] will be used to denote a type that might be [A] or [B].  We think of a term of [Family C] as being the family [fun c => a0 squiggle_t c]. *)
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

  (** Use a record type for a full step to avoid the interleaved sequence and `flip R`. *)
  Record zigzag_type : Type := {
    Pp : A -> Type; (** Stored from previous step *)
    Qp : B -> Type; (** Stored from previous step *)
    concatQPp (b : B) (a : A) (r : R a b) (q : Qp b) : Pp a; (** Stored from previous step *)
    Q : B -> Type; (** Paths of length t *)
    concatPQ (a : A) (b : B) (r : R a b) (p : Pp a) : Q b; (** t-1 -> t *)
    iotaQ (b : B) (x : Qp b) : Q b; (** t-2 -> t *)
    P : A -> Type; (** Paths of length t+1 *)
    concatQP (b : B) (a : A) (r : R a b) (q : Q b) : P a; (** t -> t+1 *)
    iotaP (a : A) (x : Pp a) : P a; (** t-1 -> t+1 *)
    concatQPQ (b : B) (a : A) (r : R a b) 
      : (compose (concatPQ a b r) (concatQPp b a r)) == (iotaQ b);
    concatPQP (a : A) (b : B) (r : R a b) 
      : (compose (concatQP b a r) (concatPQ a b r)) == (iotaP a);
  }.

  Definition zigzag_step : zigzag_type -> zigzag_type.
  Proof.
    intro z.
    destruct z.
    (* Naming them all seems to be necessary for Coq to not reorder goals. *)
    snrapply (let Pp:=_ in let Qp :=_ in let concatQPp :=_ in let Q:=_ in let concatPQ:=_ in let iotaQ:=_ in let P:=_ in let concatQP:=_ in let iotaP:=_ in let concatQPQ:=_ in let concatPQP:=_ in Build_zigzag_type Pp Qp concatQPp Q concatPQ iotaQ P concatQP iotaP concatQPQ concatPQP).
    - exact P0.
    - exact Q0.
    - exact concatQP0.
    - exact (family_step (flip R) concatQP0).
    - exact (dot_step (flip R) concatQP0).
    - exact (iota_step (flip R) concatQP0).
    - exact (family_step R concatPQ).
    - exact (dot_step R concatPQ).
    - exact (iota_step R concatPQ).
    - exact (homotopy_step (flip R) concatQP0).
    - exact (homotopy_step R concatPQ).
  Defined.

  Definition identity_zigzag_initial : zigzag_type.
  Proof.
    snrapply Build_zigzag_type.
    - exact (fun a => Empty).
    - exact (fun b => Empty).
    - intros b a r q; destruct q.
    - exact (fun b => Empty). (** Define Q0 := Empty *)
    - intros a b r q; destruct q.
    - intros b q; destruct q.
    - exact (fun a => a0 = a). (** Define P0 := Id a0 *)
    - intros b a r q; destruct q. (** Define Q0 -> P_0 *)
    - intros a q; destruct q. (** Define P_{-1} -> P0 *)
    - intros; intro q; destruct q.
    - intros; intro q; destruct q.
  Defined.

  Definition identity_zigzag : nat -> zigzag_type
    := fun n => nat_iter n zigzag_step identity_zigzag_initial.

  Definition identity_zigzag_P_seq : A -> Sequence.
  Proof.
    intro a.
    snrapply Build_Sequence.
    - intro n; exact ((identity_zigzag n).(P) a).
    - intro n; exact ((identity_zigzag (S n)).(iotaP) a).
  Defined.

  Definition identity_zigzag_Q_seq : B -> Sequence.
  Proof.
    intro b.
    snrapply Build_Sequence.
    - intro n; exact ((identity_zigzag n).(Q) b).
    - intro n; exact ((identity_zigzag (S n)).(iotaQ) b).
  Defined.

  Definition identity_zigzag_concatPQ_seq {a : A} {b : B} (r : R a b) 
    : DiagramMap (identity_zigzag_P_seq a) (succ_seq (identity_zigzag_Q_seq b)).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact ((identity_zigzag (S n)).(concatPQ) a b r).
    - intros n m g x.
      destruct g.
      transitivity ((identity_zigzag (S (S n))).(concatPQ) a b r ((identity_zigzag (S n)).(concatQP) b a r ((identity_zigzag (S n)).(concatPQ) a b r x))).
      + symmetry.
        exact ((identity_zigzag (S (S n))).(concatQPQ) b a r _).
      + apply ap.
        exact ((identity_zigzag (S n)).(concatPQP) a b r _).
  Defined.

  Definition identity_zigzag_concatQP_seq {a : A} {b : B} (r : R a b) 
    : DiagramMap (identity_zigzag_Q_seq b) (identity_zigzag_P_seq a).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact ((identity_zigzag n).(concatQP) b a r).
    - intros n m g x.
      destruct g.
      transitivity ((identity_zigzag (S n)).(concatQP) b a r ((identity_zigzag (S n)).(concatPQ) a b r ((identity_zigzag n).(concatQP) b a r x))).
      + symmetry.
        exact ((identity_zigzag (S n)).(concatPQP) a b r _).
      + apply ap.
        exact ((identity_zigzag (S n)).(concatQPQ) b a r _).
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
