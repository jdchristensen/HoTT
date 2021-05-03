Require Import Basics Types Pointed.
Require Import Truncations.
Require Import Homotopy.Suspension.
Require Import Spaces.Spheres.

Local Open Scope pointed_scope.

(** n-connected cover *)
Definition cover (n : trunc_index) (X : pType) : pType
  := @pfiber X (pTr n X) ptr.

Global Instance isconnected_cover (n : trunc_index) (X : pType)
  : IsConnected n (cover n X) := _.

(* The projection map from the n-connected cover to the type. *)
Definition cover_proj (n : trunc_index) {X : pType} : cover n X ->* X.
Proof.
  srapply Build_pMap.
  + apply pr1.
  + reflexivity.
Defined.

(* This cover projection map is n-truncated. *)
Global Instance mapinO_cover_proj (n : trunc_index) {X : pType}
  : IsTruncMap n (@cover_proj n.+1 X).
Proof.
  srapply (mapinO_pr1 n).
Defined.

(* This condition on a map X -> Y is equivalent to the induced map X<n> ->* Y<n> being an equivalence and is stronger than being n-truncated. *)
Definition isconnequiv {X Y : pType} (n : trunc_index) (f : X ->* Y)
  := forall (A : pType), IsConnected n A -> IsEquiv (fun g : A ->* X => f o* g).

(* This is stronger than being n-truncated.  CS Lemma 2.3, BVR 6.2. *)
Definition isequiv_postcompose_cover_proj (n : trunc_index) (X : pType)
  : isconnequiv n (@cover_proj n X).
Proof.
Admitted.

(* BVR 6.2 *)
Definition equiv_postcompose_cover_proj (n : nat) (X : pType) (Z : pType) `{IsConnected n Z}
  : (Z ->* cover n X) <~> (Z ->* X)
  := Build_Equiv _ _ _ (isequiv_postcompose_cover_proj n X Z _).

(* TODO: Move elsewhere. *)
Definition pequiv_pmap_s0 `{Funext} (A : pType)
  : (psphere 0 ->** A) <~>* A.
Proof.
  snrapply Build_pEquiv'.
  { snrapply equiv_adjointify.
    + intro f; exact (f South).
    + intro a.
      snrapply Build_pMap.
      { snrapply Susp_rec.
        - exact (point _).  (* North, the basepoint of [psphere 0]. *)
        - exact a.          (* South. *)
        - contradiction. }
      reflexivity.
    + cbn; reflexivity.
    + intro f.
      rapply path_pforall.
      snrapply Build_pHomotopy.
      { simpl.
        snrapply Susp_ind; simpl.
        - symmetry; apply (point_eq f).
        - reflexivity.
        - contradiction. }
      simpl.
      cbn.
      symmetry; apply concat_1p. }
  reflexivity.
Defined.

(* TODO: Move elsewhere. *)
Definition pequiv_pmap_s0_nat `{Funext} (A B : pType) (f : A ->* B)
  : f o (pequiv_pmap_s0 A) == (pequiv_pmap_s0 B) o (fun g => f o* g).
Proof.
  intro x; reflexivity.
Defined.

(** If a map is a (-1)-connected-equivalence, then it is an equivalence, since the 0-sphere is (-1)-connected. *)
Definition isequiv_connequiv_minus_one `{Funext} {X Y : pType}
  (f : X ->* Y) (HE : isconnequiv minus_two.+1 f)
  : IsEquiv f.
Proof.
  nrapply isequiv_commsq.
  - symmetry. apply pequiv_pmap_s0_nat.
  - apply HE.  exact _.
  - exact _.
  - exact _.
Defined.

(** Taking loops shifts n down by 1. *)
Definition isconnequiv_loops `{Funext} {X Y : pType} (n : trunc_index)
           (f : X ->* Y) (HE : isconnequiv n.+1 f)
  : isconnequiv n (loops_functor f).
Proof.
  intros A C.
  nrapply isequiv_commsq.
  - intro g.
    apply path_pforall.
    srapply loop_susp_adjoint_nat_r.
    exact g.
  - rapply HE.  (* Typeclass resolution knows that the suspension of A is n+1 connected. *)
  - exact _.
  - exact _.
Defined.

Definition isconnequiv_iterated_loops `{Funext} {X Y : pType} (n : nat)
  (k : trunc_index) (f : X ->* Y) (HE : isconnequiv (trunc_index_inc' k n) f)
  : isconnequiv k (iterated_loops_functor n f).
Proof.
  revert k f HE.
  induction n; intros k f HE.
  - exact HE.
  - simpl in *.
    apply isconnequiv_loops.
    rapply IHn.
    exact HE.
Defined.

(** TODO: move elsewhere. *)
Definition trunc_index_inc'_zero (n : nat)
  : trunc_index_inc' 0 n = n.
Proof.
  induction n.
  - reflexivity.
  - refine (trunc_index_inc'_succ _ _ @ (ap _ IHn)).
Defined.

Definition isequiv_iterated_loops_connequiv `{Funext} {X Y : pType} (n : nat)
  (f : X ->* Y) (HE : isconnequiv n f)
  : IsEquiv (iterated_loops_functor n.+1 f).
Proof.
  nrapply isequiv_connequiv_minus_one.
  apply isconnequiv_iterated_loops.
  refine (transport (fun k => isconnequiv k f) _ HE).
  symmetry; apply trunc_index_inc'_zero.
Defined.

Global Instance isequiv_iterated_loops_cover_proj `{Univalence}
  {n : nat} {Y : pType}
  : IsEquiv (iterated_loops_functor n.+1 (@cover_proj n Y)).
Proof.
  rapply isequiv_iterated_loops_connequiv.
  rapply isequiv_postcompose_cover_proj.
Defined.

