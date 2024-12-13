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

Section ZigzagIdentity.

  (** Construct the identity zigzag sequence. *)

  Context {A B : Type} (R : A -> B -> Type) (a0 : A).

  (** Use a record type for a full step to avoid the interleaved sequence and [flip R]. *)
  Record Zig : Type := {
    P : Family A;
    Q : Family B;
    concatQP : Dot (flip R) Q P;
  }.

  Definition Qsucc (Z : Zig) : Family B
    := family_step (flip R) (concatQP Z).

  Definition concatPQ (Z : Zig) : Dot R (P Z) (Qsucc Z)
    := dot_step (flip R) (concatQP Z).

  Definition Psucc (Z : Zig) : Family A
    := family_step R (concatPQ Z).

  Definition concatQPsucc (Z : Zig) : Dot (flip R) (Qsucc Z) (Psucc Z)
    := dot_step R (concatPQ Z).

  Definition zigzag_step (Z : Zig) : Zig
    := Build_Zig (Psucc Z) (Qsucc Z) (concatQPsucc Z).

  (** The initial zigzag: over [A] we have the identity type at [a0] and over [B] we have the empty type; these should be thought of as paths of length 0 and -1, respectively. *)
  Definition zigzag_initial : Zig.
  Proof.
    snrapply Build_Zig.
    - exact (fun a => a0 = a). (** Define [P0 := Id a0] *)
    - exact (fun b => Empty). (** Define [Q0 := Empty] *)
  - intros b a r q; destruct q. (** Define [Q0 -> P_0] *)
  Defined.

  Definition zigzag : nat -> Zig
    := fun n => nat_iter n zigzag_step zigzag_initial.

  Definition zigzag_P : A -> Sequence.
  Proof.
    intro a.
    snrapply Build_Sequence.
    - intro n; exact (P (zigzag n) a).
    - intro n. cbn. apply iota_step.
  Defined.

  Definition zigzag_Q : B -> Sequence.
  Proof.
    intro b.
    snrapply Build_Sequence.
    - intro n; exact (Q (zigzag n) b).
    - intro n. cbn. apply iota_step.
  Defined.

  Definition zigzag_gluePQ {a : A} {b : B} (r : R a b) 
    : DiagramMap (zigzag_P a) (succ_seq (zigzag_Q b)).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact (concatPQ (zigzag n) a b r).
    - intros n m g x.
      destruct g.
      lhs nrapply homotopy_step.
      apply ap.
      symmetry.
      apply homotopy_step.
  Defined.

  Definition zigzag_glueQP {a : A} {b : B} (r : R a b) 
: DiagramMap (zigzag_Q b) (zigzag_P a).
  Proof.
    snrapply Build_DiagramMap.
    - intro n; exact (concatQP (zigzag n) b a r).
    - intros n m g x.
      destruct g.
      lhs nrapply homotopy_step.
      apply ap.
      symmetry.
      apply homotopy_step.
  Defined.

  Definition zigzag_gluePQP {a : A} {b : B} (r : R a b) (n : nat)
    : (fun (x : zigzag_P a n) => x^+) == zigzag_glueQP r (S n) o zigzag_gluePQ r n
    := (homotopy_step R _ a b r).

  Definition zigzag_glueQPQ {a : A} {b : B} (r : R a b) (n : nat)
    : (fun (x : zigzag_Q b n) => x^+) == zigzag_gluePQ r n o zigzag_glueQP r n
    := (homotopy_step (flip R) _ b a r).

  (** The colimit of paths starting and ending in A. *)
  Definition zigzag_Pinf (a : A) : Type
    := Colimit (zigzag_P a).

  (** Our candidate for reflexivity: the colimit of reflexivity. *)
  Definition zigzag_refl : zigzag_Pinf a0
    := @colim _ (zigzag_P a0) 0%nat idpath.

  (** The colimit of paths starting in A and ending in B. *)
  Definition zigzag_Qinf (b : B) : Type 
    := Colimit (zigzag_Q b).

  Section GluingEquiv.

    Context {a : A} {b : B} (r : R a b).

    (** The gluing equivalence. *)
    Definition equiv_zigzag_glueinf
      : (zigzag_Pinf a) <~> (zigzag_Qinf b)
      := equiv_zigzag_glue (zigzag_glueQP r) (zigzag_gluePQ r) (zigzag_glueQPQ r) (zigzag_gluePQP r).

    Definition zigzag_gluePQinf : zigzag_Pinf a -> zigzag_Qinf b
      := equiv_zigzag_glueinf.

    Definition zigzag_glueQPinf : zigzag_Qinf b -> zigzag_Pinf a
      := equiv_zigzag_glueinf^-1.

    Definition zigzag_comp_eissect (n : nat) (p : zigzag_P a n) : (eissect equiv_zigzag_glueinf (@colim _ (zigzag_P a) n p)) = (ap (@colim _ (zigzag_P a) (S n)) (zigzag_gluePQP r n p)^) @ (@colimp _ (zigzag_P a) n _ _ p)
      := zigzag_comp_eissect (zigzag_glueQP r) (zigzag_gluePQ r) (zigzag_glueQPQ r) (zigzag_gluePQP r) n p.

    Definition zigzag_comp_eisretr (n : nat) (q : zigzag_Q b n) : (eisretr equiv_zigzag_glueinf (@colim _ (zigzag_Q b) n q)) = (ap (@colim _ (zigzag_Q b) (S n)) (zigzag_glueQPQ r n q)^) @ (@colimp _ (zigzag_Q b) n _ _ q)
      := zigzag_comp_eisretr (zigzag_glueQP r) (zigzag_gluePQ r) (zigzag_glueQPQ r) (zigzag_gluePQP r) n q.

  End GluingEquiv.

  (** Prove that the colimit of the identity zigzag is equivalent to the identity type for pushouts. *)

  (** FIXME: This is essentially [SpanPushout]. *)

  Definition relation_total : Type
    := {x : A * B | R (fst x) (snd x)}.

  Definition relation_pushout : Type.
  Proof.
    snrapply Pushout.
    + exact relation_total.
    + exact A.
    + exact B.
    + exact (fst o pr1).
    + exact (snd o pr1).
  Defined.

  Context `{Univalence}.

  (** The candidate for the identity type. *)
  Definition zigzag_family_half
    : relation_pushout -> Type
    := fam_podescent (Build_poDescent _ _ _ _ _ zigzag_Pinf zigzag_Qinf (fun x => equiv_zigzag_glueinf (pr2 x))).
End ZigzagIdentity.
