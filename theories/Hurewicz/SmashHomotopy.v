Require Import Coq.Init.Peano.
Require Import Spaces.Nat.
Require Import Basics Types Pointed.
Require Import ReflectiveSubuniverse.
Require Import Truncations.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import HomotopyGroup.
Require Import Hurewicz.HomotopyGroup2.
Require Import Hurewicz.PreGroup.

Local Open Scope pointed_scope.

(* TODO: move to Loops.v *)
Lemma iterated_loops_sum (n m : nat) (X : pType)
  : iterated_loops (n+m) X = iterated_loops n (iterated_loops m X).
Proof.
  induction n.
  1: reflexivity.
  cbn.
  exact (ap loops IHn).
Defined.

Lemma equiv_iterated_loops_sum (n m : nat) (X : pType)
  : iterated_loops (n+m) X <~>* iterated_loops n (iterated_loops m X).
Proof.
  induction n.
  1: reflexivity.
  Local Opaque loops.
  cbn.
  exact (pequiv_loops_functor IHn).
(* Or:
  apply pequiv_path.
  apply iterated_loops_sum.
*)
Defined.

Lemma equiv_iterated_loops_sum' (n m : nat) (X : pType)
  : iterated_loops (n+m) X <~>* iterated_loops m (iterated_loops n X).
Proof.
  transitivity (iterated_loops (m+n) X).
  - apply pequiv_path.
    apply (ap (fun k => iterated_loops k X) (nat_plus_comm n m)).
  - apply equiv_iterated_loops_sum.
Defined.

(* TODO: move to Groups? *)
Notation "X '->G' Y" := (GroupHomomorphism X Y) (at level 15, right associativity).

Local Open Scope mc_add_scope.

(* TODO: generalize the version in AbelianGroup.v.  The only change is in the type of A.
   Or maybe better to generalize to magmas. *)
(** Homomorphisms from a group to an abelian group form an abelian group. *)
Definition AbHom' (A : Group) (B : AbGroup) `{Funext} : AbGroup.
Proof.
  snrapply (Build_AbGroup (GroupHomomorphism A B)).
  + intros f g.
    snrapply Build_GroupHomomorphism.
    - intro x; exact (f x + g x).
    - intros x y.
      rewrite 2 grp_homo_op.
      rewrite 2 simple_associativity.
      rewrite <- (simple_associativity (f _) (g _)).
      rewrite (commutativity (g _) (f _)).
      rewrite simple_associativity.
      reflexivity.
  + snrapply Build_GroupHomomorphism.
    - intro; exact mon_unit.
    - intros x y.
      symmetry.
      apply left_identity.
  + intro f.
    snrapply Build_GroupHomomorphism.
    - intro x; exact (- f x).
    - intros x y.
      rewrite grp_homo_op.
      apply negate_sg_op_distr.
  + repeat split.
    1: exact _.
    all: hnf; intros; apply equiv_path_grouphomomorphism; intro; cbn.
    - apply associativity.
    - apply left_identity.
    - apply right_identity.
    - apply left_inverse.
    - apply right_inverse.
    - apply commutativity.
Defined.

Notation "X '->A' Y" := (AbHom' X Y) (at level 15, right associativity).

Definition magma_trunc (n : nat) (A : Magma) : Magma.
Proof.
  srapply (Build_Magma (Trunc n A)).
  intros a b.
  strip_truncations.
  exact (tr (sg_op a b)).
Defined.

Definition magmamap_to_trunc (n : nat) (A : Magma) : MagmaMap A (magma_trunc n A).
Proof.
  snrapply Build_MagmaMap.
  1: apply tr.
  apply tr.
  intros a b.
  reflexivity.
Defined.  

Definition magmamap_trunc_rec {A B : Magma} (n : nat) `{IsTrunc n B}
  : MagmaMap A B -> MagmaMap (magma_trunc n A) B.
Proof.
  intro f.
  (* Not sure why I have to spell all of this out: *)
  snrapply Build_MagmaMap.
  1: exact (Trunc_rec f).
  pose proof (magmamap_op_preserving f) as r.
  strip_truncations.
  apply tr.
  intros a0 a1.
  strip_truncations.
  cbn.
  apply r.
Defined.

Definition magmamap_trunc_functor {A B : Magma} (n : nat)
  : MagmaMap A B -> MagmaMap (magma_trunc n A) (magma_trunc n B).
Proof.
  intro f.
  rapply magmamap_trunc_rec.
  exact (magmamap_compose (magmamap_to_trunc n B) f).
Defined.

(** The theory of (merely) abelian magmas. *)

Record AbMagma := {
  abmagma_magma :> Magma;
  abmagma_isab : merely (forall x y : abmagma_magma, sg_op x y = sg_op y x)
}.

Definition AbMagmaHom (A : Magma) (B : AbMagma) `{Funext} : AbMagma.
Proof.
  snrapply Build_AbMagma.
  - snrapply (Build_Magma (MagmaMap A B)).
    intros f g.
    snrapply Build_MagmaMap.
    + intro x; exact (f x + g x).
    + pose proof (magmamap_op_preserving f) as r.
      pose proof (magmamap_op_preserving g) as s.
      strip_truncations.
      apply tr.
      intros x y.
      rewrite r, s.
      (* Oh, no, magmas aren't associative! *)
(*
      rewrite 2 simple_associativity.
      rewrite <- (simple_associativity (f _) (g _)).
      rewrite (commutativity (g _) (f _)).
      rewrite simple_associativity.
      reflexivity.
  + snrapply Build_GroupHomomorphism.
    - intro; exact mon_unit.
    - intros x y.
      symmetry.
      apply left_identity.
  + intro f.
    snrapply Build_GroupHomomorphism.
    - intro x; exact (- f x).
    - intros x y.
      rewrite grp_homo_op.
      apply negate_sg_op_distr.
  + repeat split.
    1: exact _.
    all: hnf; intros; apply equiv_path_grouphomomorphism; intro; cbn.
    - apply associativity.
    - apply left_identity.
    - apply right_identity.
    - apply left_inverse.
    - apply right_inverse.
    - apply commutativity.
Defined.
 *)
Abort.

Definition sm `{Funext} (X Y Z : pType) (n m : nat) :
  (X ->* (Y ->** Z)) -> (Pi n.+1 X -> Pi m.+1 Y -> Pi (n.+1 + m.+1)%nat Z).
(* TODO:
   RHS maps should be group homomorphisms.
   Top-level map should maybe be pointed?  Wait and see.
   Intermediate steps should be magma maps or pointed magma maps.
   Maybe express it as a composite, so that we can reason about it:
   - show each step is natural
   - show composite is an equivalence under certain hypotheses
*)
Proof.
  intro f.
  (* Goal is fifth line of equation (2.1) in CS. *)
  rapply Trunc_ind.
  intro lx.
  apply Trunc_functor.
  fold Peano.plus.
  (* Goal is fourth line of equation (2.1) in CS. *)
  intro ly.
  apply (equiv_iterated_loops_sum' (n.+1) (m.+1) _)^-1.
  revert ly.
  (* Goal is third line of equation (2.1) in CS. *)
  refine (pointed_fun (iterated_loops_functor m.+1 _)).
  (* Goal is second line of equation (2.1) in CS. *)
  Local Opaque iterated_loops.
  apply equiv_iterated_magma_loops_in.  (* Need iterated version. *)
  revert lx.
  (* Goal is RHS of first line of equation (2.1) in CS. *)
  cbn.
  exact (iterated_loops_functor n.+1 f).
Defined.

(* A version with group homomorphisms, in progress: *)
Definition sm' `{Funext} (X Y Z : pType) (n m : nat) :
  (X ->* (Y ->** Z)) -> (Pi n.+1 X ->G Pi m.+1 Y ->A Pi' (n.+2 + m)%nat Z).
(* TODO:
   RHS maps should be group homomorphisms.
   Top-level map should maybe be pointed?  Wait and see.
   Intermediate steps should be magma maps or pointed magma maps.
   Maybe express it as a composite, so that we can reason about it:
   - show each step is natural
   - show composite is an equivalence under certain hypotheses
*)
Proof.
  intro f.
  (* Goal is fifth line of equation (2.1) in CS. *)
  apply (equiv_grp_homo_magmamap _ _)^-1%equiv.
  (* Conveniently, [magma_trunc 0 (magma_loops X)] is definitionally equal to [group_to_magma (Pi 1 X)] as magmas. *)
  refine (@magmamap_trunc_rec (magma_loops _) _ 0 _ _).
Abort.
