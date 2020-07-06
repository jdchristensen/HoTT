(* These things should probably be moved to Homotopy/Smash.v. *)
(* Also, there's a typo there:  smash_rec_beta_gluer should be capitalized. *)

Require Import Basics.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pTrunc.
Require Import Cubical.
Require Import Homotopy.Smash.
Require Import Truncations NullHomotopy.

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

(* Avoid unfolding Smash.  Also speeds up the [Defined] at the end. *)
Opaque Smash.

Lemma pswap_natural {A B X Y : pType} (f : A ->* X) (g : B ->* Y)
  : pswap o* Smash_functor f g ==* Smash_functor g f o* pswap.
Proof.
  destruct X as [X x0].
  destruct Y as [Y y0].
  destruct f as [f f0].
  destruct g as [g g0].
  unfold pointed_type, point, ispointed_type in *.
  cbn in f, g, f0, g0.
  induction f0.
  induction g0.
  unfold pointed_type, point, ispointed_type.
  (* The above lines are also accomplished by [pointed_reduce], but this way of doing it makes the goal look cleaner. *)
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

Transparent Smash.

(** Lemma 2.31 [van Doorn, Theorem 4.3.28] *)
(** We take this as an axiom. *)
(** For now, no naturality conditions, just an equivalence. *)
Lemma equiv_pmap_curry (X Y Z : pType)
  : (X ->** (Y ->** Z)) <~>* (Smash X Y ->** Z).
Proof.
Admitted.

(** Lemma 2.27 [Buchholtz-van Doorn-Rijke, Corollary 4.3] *)
(** We take this as an axiom. *)
Global Instance istrunc_ppmap {m n : trunc_index} (X Y : pType)
  `{!IsConnected m.+1 X} `{!IsTrunc (n +2+ m).+1 Y}
  : IsTrunc n.+1 (X ->* Y).
Proof.
Admitted.

Global Instance contr_pmap_smash {n m : trunc_index} (X Y Z : pType)
  `{!IsConnected n.+1 X} `{!IsConnected m.+1 Y} `{!IsTrunc (n +2+ m).+1 Z}
  : Contr (Smash X Y ->* Z).
Proof.
  rapply (contr_equiv' _ (equiv_pmap_curry _ _ _)).
  rapply contr_inhabited_hprop.
  exact (point _).
Defined.

(** Corollary 2.32: Connectivity of the smash product.  With different indexing, this says that for [n] and [m] natural numbers, [X] [n-1]-connected and [Y] [m-1]-connected, the smash product of [X] and [Y] is [n+m-1]-connected. *)
Corollary isconnected_smash {n m : trunc_index} (X Y : pType)
  `{!IsConnected n.+1 X} `{!IsConnected m.+1 Y}
  : IsConnected ((n +2+ m).+1) (Smash X Y).
Proof.
  (** To show this type is connected, it is enough to show that the truncation map is nullhomotopic. *)
  apply isconnected_from_elim_to_O.
  (** The nullhomotopy will be to a constant map at the basepoint. *)
  exists (point _).
  (** We need an unpointed homotopy, but it is easier to find a pointed homotopy between the corresponding pointed maps. *)
  apply (pointed_htpy (f:=ptr) (g:=pconst)).
  (** Pointed homotopies can be obtained from paths in the pointed mapping space. *)
  apply phomotopy_path.
  (** By [contr_pmap_smash] such a path exists since the type is contractible. *)
  apply path_contr.
Defined.
