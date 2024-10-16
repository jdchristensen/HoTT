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

Definition pred_type_or_empty (P : nat -> Type) (t : nat) : Type.
Proof.
  induction t.
  - exact Empty.
  - exact (P t).
Defined.

Record zigzag_type {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) 
  : Type := {
    Pp : A -> Type; (** Stored from previous step *)
    Qp : B -> Type; (** Stored from previous step *)
    concatQPp (a : A) (b : B) (r : R a b) (q : Qp b) : Pp a; (** Stored from previous step *)
    Q : B -> Type; (** Paths of length t *)
    concatPQ (a : A) (b : B) (r : R a b) (p : Pp a) : Q b; (** t-1 -> t *)
    iotaQ (b : B) (x : Qp b) : Q b; (** t-2 -> t *)
    P : A -> Type; (** Paths of length t+1 *)
    concatQP (a : A) (b : B) (r : R a b) (q : Q b) : P a; (** t -> t+1 *)
    iotaP (a : A) (x : Pp a) : P a; (** t-1 -> t+1 *)
    concatQPQ (a : A) (b : B) (r : R a b) 
      : (compose (concatPQ a b r) (concatQPp a b r)) == (iotaQ b);
    concatPQP (a : A) (b : B) (r : R a b) 
      : (compose (concatQP a b r) (concatPQ a b r)) == (iotaP a);
  }.

Definition zigzag_step {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (z : zigzag_type R a0) 
  : zigzag_type R a0.
Proof.
  destruct z.
  snrapply (let Pp:=_ in let Qp :=_ in let concatQPp :=_ in let Q:=_ in let concatPQ:=_ in let iotaQ:=_ in let P:=_ in let concatQP:=_ in let iotaP:=_ in let concatQPQ:=_ in let concatPQP:=_ in Build_zigzag_type A B R a0 Pp Qp concatQPp Q concatPQ iotaQ P concatQP iotaP concatQPQ concatPQP).
  - exact P0.
  - exact Q0.
  - exact concatQP0.
  - intros b. (** Constructing Q_t *)
    snrapply Pushout.
    + exact (sig (fun a => prod (R a b) (Q0 b))).
    + exact (Q0 b).
    + exact (sig (fun a => prod (R a b) (P0 a))).
    + intro x.
      exact (snd (pr2 x)).
    + intro a.
      destruct a as [a [r p]].
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
      destruct b as [b [r p]].
      exact (b ; (r , concatPQ a b r p)).
  - intros a b r p. (** Consructing Q_t -> P_t (concatQP) *)
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
    + intro q.
      unfold concatPQ.
      unfold iotaQ.
      symmetry.
      unfold incl.
      exact (pglue (a ; (r , q))).
    + intro q.
      apply ap.
      exact (H q).
  - intros a b r.
    transparent assert (incl : ((Pp a) -> (sig (fun b' => prod (R a b') (Pp a))))). {
      intro p'.
      exact (b ; (r , p')).
    }
    transparent assert (proj : ((sig (fun b' => prod (R a b') (Pp a))) -> (Pp a))). {
      intro x.
      destruct x.
      destruct proj2.
      exact snd.
    }
    transparent assert (H : (proj o incl == idmap)). {
      intro x.
      reflexivity.
    }
    transitivity ((iotaP a) o proj o incl).
    + intro q.
      unfold concatPQ.
      unfold iotaQ.
      symmetry.
      unfold incl.
      exact (pglue (b ; (r , q))).
    + intro q.
      apply ap.
      exact (H q).
Defined.

Definition identity_zigzag_initial {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) : zigzag_type R a0.
Proof.
  snrapply (Build_zigzag_type A B R a0).
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
  - intros.
    intro q.
    destruct q.
  - intros.
    intro q.
    destruct q.
Defined.

Definition identity_zigzag {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (t : nat) 
  : zigzag_type R a0 := 
  nat_iter t (fun x => zigzag_step R a0 x) (identity_zigzag_initial R a0).

Definition identity_zigzag_P {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) (t : nat) 
  : Type := 
  (identity_zigzag R a0 t).(P R a0) a.

Definition identity_zigzag_iotaP {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) (t : nat) 
  : (identity_zigzag_P R a0 a t) -> (identity_zigzag_P R a0 a (S t)) := 
  (identity_zigzag R a0 (S t)).(iotaP R a0) a.

Definition identity_zigzag_P_seq {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) : Sequence.
Proof.
  snrapply Build_Sequence.
  - exact (identity_zigzag_P R a0 a).
  - exact (identity_zigzag_iotaP R a0 a).
Defined.

Definition identity_zigzag_Q {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (b : B) (t : nat) : Type := 
  (identity_zigzag R a0 t).(Q R a0) b.

Definition identity_zigzag_iotaQ {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (b : B) (t : nat) 
  : (identity_zigzag_Q R a0 b t) -> (identity_zigzag_Q R a0 b (S t)) := 
  (identity_zigzag R a0 (S t)).(iotaQ R a0) b.

Definition identity_zigzag_Q_seq {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (b : B) : Sequence.
Proof.
  snrapply Build_Sequence.
  - exact (identity_zigzag_Q R a0 b).
  - exact (identity_zigzag_iotaQ R a0 b).
Defined.

Definition identity_zigzag_concatQP {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) (b : B) (r : R a b) (t : nat) 
  : (identity_zigzag_Q R a0 b t) -> (identity_zigzag_P R a0 a t) := 
  (identity_zigzag R a0 t).(concatQP R a0) a b r.


Definition identity_zigzag_concatPQ {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) (b : B) (r : R a b) (t : nat) : 
  (identity_zigzag_P R a0 a t) -> (identity_zigzag_Q R a0 b (S t)) := 
  (identity_zigzag R a0 (S t)).(concatPQ R a0) a b r.

Definition identity_zigzag_concatQPQ {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) (b : B) (r : R a b) (t : nat) : 
  (compose (identity_zigzag_concatPQ R a0 a b r t) 
    (identity_zigzag_concatQP R a0 a b r t)) 
  == (identity_zigzag_iotaQ R a0 b t) := 
  (identity_zigzag R a0 (S t)).(concatQPQ R a0) a b r.

Definition identity_zigzag_concatPQP {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) (b : B) (r : R a b) (t : nat) : 
  (compose (identity_zigzag_concatQP R a0 a b r (S t)) 
    (identity_zigzag_concatPQ R a0 a b r t)) 
  == (identity_zigzag_iotaP R a0 a t) := 
  (identity_zigzag R a0 (S t)).(concatPQP R a0) a b r.

Definition identity_zigzag_seq_concatQP {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) (b : B) (r : R a b) : 
  DiagramMap (identity_zigzag_Q_seq R a0 b) (identity_zigzag_P_seq R a0 a).
Proof.
  snrapply Build_DiagramMap.
  - intro t.
    exact (identity_zigzag_concatQP R a0 a b r t).
  - intros t p q x.
    destruct q.
    simpl.
    transitivity (identity_zigzag_concatQP R a0 a b r (S t) (identity_zigzag_concatPQ R a0 a b r t (identity_zigzag_concatQP R a0 a b r t x))).
    + symmetry.
      exact (identity_zigzag_concatPQP R a0 a b r t _).
    + apply ap.
      exact (identity_zigzag_concatQPQ R a0 a b r t _).
Defined.

Definition identity_zigzag_seq_concatPQ {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) (a : A) (b : B) (r : R a b) : DiagramMap (identity_zigzag_P_seq R a0 a) (succ_seq (identity_zigzag_Q_seq R a0 b)).
Proof.
  snrapply Build_DiagramMap.
  - intro t.
    simpl.
    Compute (Graph.graph0 sequence_graph).
    exact (identity_zigzag_concatPQ R a0 a b r t).
  - intros t p q x.
    destruct q.
    simpl.
    transitivity (identity_zigzag_concatPQ R a0 a b r (S t) (identity_zigzag_concatQP R a0 a b r (S t) (identity_zigzag_concatPQ R a0 a b r t x))).
    + symmetry.
      exact (identity_zigzag_concatQPQ R a0 a b r (S t) _).
    + apply ap.
      exact (identity_zigzag_concatPQP R a0 a b r t _).
Defined.

Definition identity_zigzag_Pinf {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) : Type := 
  Colimit (identity_zigzag_P_seq R a0 a).

Definition identity_zigzag_Qinf {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (b : B) : Type := 
  Colimit (identity_zigzag_Q_seq R a0 b).

Definition identity_zigzag_Pswap {A : Type} {B : Type} (R : A -> B -> Type) 
  (a0 : A) (a : A) (t : nat) 
  : (identity_zigzag_P R a0 a t) <~> (identity_zigzag_P R a a0 t).
Proof.
  induction t.
  + simpl.
    snrapply Build_Equiv.
    2: exact (isequiv_path_inverse a0 a).
  + simpl.
    snrapply Build_Equiv.
Admitted.

Definition identity_zigzag_concatQPinf `{Funext} {A : Type} {B : Type} 
  (R : A -> B -> Type) (a0 : A) (a : A) (b : B) (r : R a b) 
  : (identity_zigzag_Qinf R a0 b) -> (identity_zigzag_Pinf R a0 a) := 
  functor_colimit (identity_zigzag_seq_concatQP R a0 a b r) _ _.

Definition identity_zigzag_concatPQinf `{Funext} {A : Type} {B : Type} 
  (R : A -> B -> Type) (a0 : A) (a : A) (b : B) (r : R a b) 
  : (identity_zigzag_Pinf R a0 a) -> (identity_zigzag_Qinf R a0 b) := 
  (colim_succ_seq_to_colim_seq _) 
  o (functor_colimit (identity_zigzag_seq_concatPQ R a0 a b r) _ _ ).

Section Death.
  Context `{Funext} {A : Type} {B : Type} (R : A -> B -> Type) (a0 : A) 
    (a : A) (b : B) (r : R a b).

  Check (identity_zigzag_concatPQinf).

End Death.

Definition identity_zigzag_concatinf_retr `{Univalence} {A : Type} {B : Type} 
  (R : A -> B -> Type) (a0 : A) (a : A) (b : B) (r : R a b) 
  : (identity_zigzag_concatPQinf R a0 a b r) 
    o (identity_zigzag_concatQPinf R a0 a b r) 
    == idmap.
Proof.
  snrapply Colimit_ind.
  - simpl.
    intros t p.
    transitivity (inj (identity_zigzag_Q_seq R a0 b) (S t) (identity_zigzag_concatPQ R a0 a b r t (identity_zigzag_concatQP R a0 a b r t p))).
    + reflexivity.
    + transitivity (inj (identity_zigzag_Q_seq R a0 b) (S t) (identity_zigzag_iotaQ R a0 b t p)).
      * apply ap.
        exact (identity_zigzag_concatQPQ R a0 a b r t p).
      * apply (glue (identity_zigzag_Q_seq R a0 b)).
  - intros t n q p.
    destruct q.
    admit.
Admitted.

Definition identity_zigzag_concatinf_sec `{Univalence} {A : Type} {B : Type}
  (R : A -> B -> Type) (a0 : A) (a : A) (b : B) (r : R a b) 
  : (identity_zigzag_concatQPinf R a0 a b r) 
    o (identity_zigzag_concatPQinf R a0 a b r) 
    == idmap.
Proof.
Admitted.

Definition isequiv_identity_zigzag_concatinf `{Univalence} {A : Type} 
  {B : Type} (R : A -> B -> Type) (a0 : A) (a : A) (b : B) (r : R a b) 
  : IsEquiv (identity_zigzag_concatPQinf R a0 a b r).
Proof.
  snrapply isequiv_adjointify.
  2: exact (identity_zigzag_concatinf_retr R a0 a b r).
  exact (identity_zigzag_concatinf_sec R a0 a b r).
Defined.

Definition relation_type {A : Type} {B : Type} (R : A -> B -> Type) 
  : Type := { a : A | { b : B | R a b}}.

Definition relation_pr1 {A: Type} {B : Type} (R : A -> B -> Type) 
  : (relation_type R) -> A := pr1.

Definition relation_pr2 {A: Type} {B : Type} (R : A -> B -> Type) 
  : (relation_type R) -> B.
Proof.
  intro a.
  destruct a as [a b].
  exact (pr1 b).
Defined.

Definition relation_flip {A : Type} {B : Type} (R : A -> B -> Type) 
  : forall (b : B)  (a : A), Type.
Proof.
  intros b a.
  exact (R a b).
Defined.

Definition Pushout_relation {A : Type} {B : Type} (R : A -> B -> Type) : Type.
Proof.
  snrapply Pushout.
  - exact (relation_type R).
  - exact A.
  - exact B.
  - intro a.
    destruct a as [a _].
    exact a.
  - intro a.
    destruct a as [a [b r]].
    exact b.
Defined.

Definition identity_zigzag_family `{Univalence} {A : Type} {B : Type} 
  (R : A -> B -> Type) : (Pushout_relation R) -> (Pushout_relation R) -> Type.
Proof.
  snrapply Pushout_rec.
  - intro x.
    snrapply Pushout_rec.
    + intro y.
      exact (identity_zigzag_Pinf R x y).
    + intro y.
      exact (identity_zigzag_Qinf R x y).
    + intro r.
      destruct r as [a [b r]].
      snrapply path_universe_uncurried.
      snrapply Build_Equiv.
      * exact (identity_zigzag_concatPQinf R x a b r).
      * exact (isequiv_identity_zigzag_concatinf R x a b r).
  - intro x.
    pose (R' := (relation_flip R)).
    snrapply Pushout_rec.
    + intro y.
      exact (identity_zigzag_Qinf R' x y).
    + intro y.
      exact (identity_zigzag_Pinf R' x y).
    + intro r.
      destruct r as [a [b r]].
      snrapply path_universe_uncurried.
      symmetry.
      snrapply Build_Equiv.
      * exact (identity_zigzag_concatPQinf R' x b a r).
      * exact (isequiv_identity_zigzag_concatinf R' x b a r).
  - intro r.
    destruct r as [a [b r]].
    snrapply path_forall.
    snrapply Pushout_ind.
    + intro a'.
      simpl.

      




    


      
