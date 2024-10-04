Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.

Definition pred_type_or_empty (P : nat -> Type) (t : nat) : Type.
Proof.
  induction t.
  - exact Empty.
  - exact (P t).
Defined.

Record zigzag_type {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) : Type := {
  Pp : A -> Type; (** Stored from previous step *)
  Qp : B -> Type; (** Stored from previous step *)
  concatQPp (a : A) (b : B) (r : R a b) (q : Qp b) : Pp a; (** Stored from previous step *)
  Q : B -> Type; (** Paths of length t *)
  concatPQ (a : A) (b : B) (r : R a b) (p : Pp a) : Q b; (** t-1 -> t *)
  iotaQ (b : B) (x : Qp b) : Q b; (** t-2 -> t *)
  P : A -> Type; (** Paths of length t+1 *)
  concatQP (a : A) (b : B) (r : R a b) (q : Q b) : P a; (** t -> t+1 *)
  iotaP (a : A) (x : Pp a) : P a; (** t-1 -> t+1 *)
}.

Definition identity_zigzag {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (t : nat) : zigzag_type R a0.
Proof.
  induction t.
  - snrapply Build_zigzag_type.
    + exact (fun a => Empty).
    + exact (fun b => Empty).
    + intros a b r e.
      destruct e.
    + exact (fun b => Empty).
    + intros a b r e.
      destruct e.
    + intros b e.
      destruct e.
    + exact (fun a => a0 = a).
    + intros a b r e.
      destruct e.
    + intros a e.
      destruct e.
  - destruct IHt.
    snrapply Build_zigzag_type.
    + exact P0.
    + exact Q0.
    + exact concatQP0.
    + intros b.
      snrapply Pushout.
      * exact (sig (fun a => prod (R a b) (Q0 b))).
      * exact (Q0 b).
      * exact (sig (fun a => prod (R a b) (P0 a))).
      * intro x.
        exact (snd (pr2 x)).
