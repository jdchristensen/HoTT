Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Sequence.
Require Import WildCat.

Set Implicit Arguments.

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
  concatQPQ (a : A) (b : B) (r : R a b) : (compose (concatPQ r) (concatQPp r)) == (iotaQ (b := b));
  concatPQP (a : A) (b : B) (r : R a b) : (compose (concatQP r) (concatPQ r)) == (iotaP (a := a));
}.

Definition zigzag_step {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (z : zigzag_type R a0) : zigzag_type R a0.
Proof.
  destruct z.
  snrapply (let Pp:=_ in let Qp :=_ in let concatQPp :=_ in let Q:=_ in let concatPQ:=_ in let iotaQ:=_ in let P:=_ in let concatQP:=_ in let iotaP:=_ in let concatQPQ:=_ in let concatPQP:=_ in Build_zigzag_type R a0 Pp Qp concatQPp Q concatPQ iotaQ P concatQP iotaP concatQPQ concatPQP).
  - exact P0.
  - exact Q0.
  - exact concatQP0.
  - intros b. (** Constructing Q_t *)
    snrapply Pushout.
    +exact (sig (fun a => prod (R a b) (Q0 b))).
    + exact (Q0 b).
    + exact (sig (fun a => prod (R a b) (P0 a))).
    + intro x.
      exact (snd (pr2 x)).
    + intro a.
      destruct a as [a p2].
      destruct p2 as [r p].
      exact (a ; (r , (concatQP0 a b r p))).
  - intros a b r p. (** Constructing P_{t-1} -> Q_t (concatPQ) *)
    snrapply pushr.
    exact (a ; (r , p)).
  - intros b. (** Constructing Q_{t-1} -> Q_t *)
    exact pushl.
  - intro a. (** Constructing P_t *)
    snrapply Pushout.
    + exact (sig (fun b => prod (R a b) (P0 a))).
    + exact (P0 a).
    + exact (sig (fun b => prod (R a b) (Q b))).
    + intro x.
      exact (snd (pr2 x)).
    + intro b.
      destruct b as [b p2].
      destruct p2 as [r p].
      exact (b ; (r , concatPQ a b r p)).
  - intros a b r p. (** Consructin Q_t -> P_t (concatQP) *)
    snrapply pushr.
    exact (b ; (r , p)).
  - intros a. (** Constructing P_{t-1} -> P_t *)
    exact pushl.
  - intros a b r.
    transparent assert (incl : ((Qp b) -> (sig (fun a' => prod (R a' b) (Qp b))))). {
      intro q'.
      exact (a ; (r , q')).
    }
    transparent assert (proj : ((sig (fun a' => prod (R a' b) (Qp b))) -> (Qp b))). {
      intro x.
      destruct x.
      destruct proj2.
      exact snd.
    }
    transparent assert (H : (proj o incl == idmap)). {
      intro x.
      reflexivity.
    }
    transitivity ((iotaQ b) o proj o incl).
    + admit.
    + intro q.
      apply ap.
      exact 




Definition identity_zigzag_initial {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) : zigzag_type R a0.
Proof.
  snrapply (Build_zigzag_type R a0).
  - exact (fun a => Empty).
  - exact (fun b => Empty).
  - intros a b r q.
    destruct q.
  - exact (fun b => Empty). (** Define Q_0 := Empty *)
  - intros a b r q. (** Define P_{-1} -> Q_0 *)
    destruct q.
  - intros b q. (** Define Q_{-1} -> Q_0 *)
    destruct q.
  - exact (fun a => a0 = a). (** Define P_0 := Id a0 *)
  - intros a b r q. (** Define Q_0 -> P_0 *)
    destruct q.
  - intros a p. (** Define P_{-1} -> P_0 *)
    destruct p.
Defined.

Definition identity_zigzag {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (t : nat) : zigzag_type R a0 := nat_iter t (fun x => zigzag_step x) (identity_zigzag_initial R a0).

Definition identity_zigzag_P {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (a : A) (t : nat) : Type := (identity_zigzag R a0 t).(P) a.

Definition identity_zigzag_iotaP {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (a : A) (t : nat) : (identity_zigzag_P R a0 a t) -> (identity_zigzag_P R a0 a (S t)) := (identity_zigzag R a0 (S t)).(iotaP) a.

Definition identity_zigzag_P_seq {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (a : A) : Sequence.
Proof.
  snrapply Build_Sequence.
  - exact (identity_zigzag_P R a0 a).
  - exact (identity_zigzag_iotaP R a0 a).
Defined.

Definition identity_zigzag_Q {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (b : B) (t : nat) : Type := (identity_zigzag R a0 t).(Q) b.

Definition identity_zigzag_iotaQ {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (b : B) (t : nat) : (identity_zigzag_Q R a0 b t) -> (identity_zigzag_Q R a0 b (S t)) := (identity_zigzag R a0 (S t)).(iotaQ) b.

Definition identity_zigzag_Q_seq {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (b : B) : Sequence.
Proof.
  snrapply Build_Sequence.
  - exact (identity_zigzag_Q R a0 b).
  - exact (identity_zigzag_iotaQ R a0 b).
Defined.

Definition identity_zigzag_concatQP {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (a : A) (b : B) (r : R a b) (t : nat) : (identity_zigzag_Q R a0 b t) -> (identity_zigzag_P R a0 a t) := (identity_zigzag R a0 t).(concatQP) a b r.


Definition identity_zigzag_concatPQ {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (a : A) (b : B) (r : R a b) (t : nat) : (identity_zigzag_P R a0 a t) -> (identity_zigzag_Q R a0 b (S t)) := (identity_zigzag R a0 (S t)).(concatPQ) a b r.

Definition identity_zigzag_concatQPQ {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (a : A) (b : B) (r : R a b) (t : nat) : (compose (identity_zigzag_concatPQ R a0 a b r t) (identity_zigzag_concatQP R a0 a b r t)) == (identity_zigzag_iotaQ R a0 b t).
Proof.
  intro p.
  induction t.
  - destruct p.
  - 

