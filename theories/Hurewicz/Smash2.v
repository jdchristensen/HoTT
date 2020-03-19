(* These things should probably be moved to Homotopy/Smash.v. *)
(* Also, there's a typo there:  smash_rec_beta_gluer should be capitalized. *)

Require Import Basics.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Cubical.
Require Import Homotopy.Smash.

Local Open Scope pointed_scope.

Definition Smash_functor {A B X Y : pType} (f : A ->* X) (g : B ->* Y)
  : Smash A B ->* Smash X Y.
Proof.
  srapply Build_pMap.
  1: {
    srefine (Smash_rec _ auxl auxr _ _).
    - intros a b.
      exact (sm (f a) (g b)).
    - intro b.  simpl.
      refine (_ @ gluel (f b)).
      refine (ap _ (point_eq g)).
    - intro a.  simpl.
      refine (_ @ gluer (g a)).
      apply ap10.
      refine (ap _ (point_eq f)).
  }
  simpl.
  refine (_ @ _).
  1: exact (ap (fun x => sm x (g (point B))) (point_eq f)).
  exact (ap (fun y => sm (point X) y) (point_eq g)).
Defined.

(** Symmetry of the smash product. *)

Definition swap {X Y : pType} : Smash X Y -> Smash Y X.
Proof.
  apply (Smash_rec (fun a => fun b => sm b a) auxr auxl).
  - apply gluer.
  - apply gluel.
Defined.

Definition pswap {X Y : pType} : Smash X Y ->* Smash Y X.
Proof.
  srapply Build_pMap.
  - exact swap.
  - reflexivity.
Defined.

Theorem swap_swap {X Y : pType} : forall xy : Smash X Y, swap (swap xy) = xy.
Proof.
  snrapply Smash_ind. 1,2,3: reflexivity.
  - simpl.
    intro x.
    apply equiv_dp_paths_FFlr.
    rewrite Smash_rec_beta_gluel.
    rewrite smash_rec_beta_gluer.
    rewrite concat_p1.
    apply concat_Vp.
  - simpl.
    intro y.
    apply equiv_dp_paths_FFlr.
    rewrite smash_rec_beta_gluer.
    rewrite Smash_rec_beta_gluel.
    rewrite concat_p1.
    apply concat_Vp.
Defined.

Theorem pswap_pswap {X Y : pType} : @pswap Y X o* @pswap X Y ==* pmap_idmap.
Proof.
  srapply Build_pHomotopy.
  - exact swap_swap.
  - reflexivity.
Defined.

Theorem isequiv_swap `{Funext} {X Y : pType} : IsEquiv (@swap X Y).
Proof.
  srapply isequiv_adjointify.
  - apply swap.
  - rapply swap_swap.
  - rapply swap_swap.
Defined.

Lemma pswap_natural {A B X Y : pType} (f : A ->* X) (g : B ->* Y)
  : pswap o* Smash_functor f g ==* Smash_functor g f o* pswap.
Proof.
  (* Avoid unfolding Smash.  Also speeds up the [Defined] at the end. *)
  Opaque Smash.
  destruct X as [X x0].
  destruct Y as [Y y0].
  destruct f as [f f0].
  destruct g as [g g0].
  unfold pointed_type, point, ispointed_type in *.
  induction f0.
  induction g0.
  unfold pointed_type, point, ispointed_type.
(* The above lines are also accomplished by [pointed_reduce], but this way of
   doing it makes the goal look cleaner. *)
  srapply Build_pHomotopy.
  + srapply Smash_ind.
    1, 2, 3: reflexivity.
    - intro a.  cbn.
      apply equiv_dp_paths_FlFr.
      (* Using [abstract] greatly speeds up the [Defined]. *)
      abstract (
          rewrite ap_compose;
          rewrite (ap_compose swap);
          do 2 rewrite Smash_rec_beta_gluel;
          rewrite smash_rec_beta_gluer;
          do 2 rewrite concat_1p;
          rewrite concat_p1;
          rewrite Smash_rec_beta_gluel;
          apply concat_Vp).
    - intro b.  cbn.
      apply equiv_dp_paths_FlFr.
      abstract (
          rewrite ap_compose;
          rewrite (ap_compose swap);
          do 2 rewrite smash_rec_beta_gluer;
          rewrite Smash_rec_beta_gluel;
          do 2 rewrite concat_1p;
          rewrite concat_p1;
          rewrite smash_rec_beta_gluer;
          apply concat_Vp).
  + reflexivity.
Defined.

(* The last Lemma and Corollary from Section 2.6 still need to be done. *)
