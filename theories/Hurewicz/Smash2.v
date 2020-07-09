(* These things should probably be moved to Homotopy/Smash.v. *)
(* Also, there's a typo there:  smash_rec_beta_gluer should be capitalized. *)

Require Import Basics.
Require Import Pointed.Core.
Require Import Pointed.pMap.
Require Import Pointed.pTrunc.
Require Import Pointed.pEquiv.
Require Import Hurewicz.Ptd.
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

(** This is the pointed versions of the [sm] map.  We should be able to use [psm] to define one of the maps in [pequiv_pmap_uncurry] below, but it's not so straightforward. *)
(** Is [Funext] necessary? *)
Definition psm `{Funext} (X Y : pType) : X ->* (Y ->** Smash X Y).
Proof.
  snrapply Build_pMap.
  - intro x.
    snrapply Build_pMap.
    + intro y.
      exact (sm x y).
    + simpl.
      refine (gluel _ @ (gluel _)^).
  - simpl.
    apply path_pforall.
    snrapply Build_pHomotopy.
    + intro y.  cbn.
      refine (gluer _ @ (gluer _)^).
    + cbn.
      refine (concat_pV _ @ _).
      exact (whiskerR (concat_pV _) 1)^.
Defined.

(** In our application, [XY] is the smash product, [bp] is its basepoint, [al] is [auxl], [ar] is [auxr], [gl] is [gluel (point X)], [gr] is [gluer (point Y)] and [z] is [point Z]. *)
Local Lemma uncurry_helper {XY Z : Type} {bp al ar} (gl : bp = al) (gr : bp = ar) (z : Z)
 : (ap_const (gr @ gr^) z)^ =
   (concat_p1 (ap (fun _ : XY => z) (gl @ gl^)) @ ap_const (gl @ gl^) z)^
   @ (ap (ap (fun _ => z)) (concat_pV gr @ (concat_pV gl)^)
         @ (concat_p1 (ap (fun _ => z) (gl @ gl^)))^)^.
Proof.
  destruct gl, gr.  reflexivity.
Defined.

(** Lemma 2.31 [van Doorn, Theorem 4.3.28] *)
(** We define the maps, but take it as an axiom that they are inverse to each other. *)
(** For now, no naturality conditions, just an equivalence. *)
Lemma pequiv_pmap_uncurry `{Funext} (X Y Z : pType)
  : (X ->** (Y ->** Z)) <~>* (Smash X Y ->** Z).
Proof.
  snrapply pequiv_adjointify.
  (* We first define the pointed map from left to right. *)
  - snrapply Build_pMap.
    + intro f.
      snrapply Build_pMap.
      * snrapply (Smash_rec (fun x y => f x y)).
        -- exact (point Z).
        -- exact (point Z).
        -- intro x.
           apply point_eq.
        -- intro y.
           refine (ap (fun g : Y ->* Z => g y) (point_eq f)).
      * lazy.
        apply point_eq.
    + cbn.
      apply path_pforall.
      snrapply Build_pHomotopy.
      * cbn.
        snrapply Smash_ind; try reflexivity.
        -- intro x.
           cbn.
           apply equiv_dp_paths_Fl.
           apply moveR_Vp.
           symmetry.
           refine (concat_p1 _ @ _).
           rapply Smash_rec_beta_gluel.
        -- intro y.
           cbn.
           apply equiv_dp_paths_Fl.
           apply moveR_Vp.
           symmetry.
           refine (concat_p1 _ @ _).
           rapply smash_rec_beta_gluer.
      * cbn.
        reflexivity.
  (* Now we define the pointed map from right to left as precomposition with [psm], in a multivariable sense. *)
  - exact (nested_pprecompose Z (psm X Y)).
  (* Next we have to prove that the two composites are equal to the identity maps, but it's complicated. *)
  (* Note that [pequiv_adjointify] asks us to prove more than is necessary.  To get a pointed equivalence, we need the first map to be pointed, but then we only need to show that its underlying map is an unpointed equivalence.  Similarly, some of the things not yet done are asking for more than is needed. *)
Admitted.

(** Lemma 2.27 [Buchholtz-van Doorn-Rijke, Corollary 4.3] *)
(** We take this as an axiom. *)
Global Instance istrunc_ppmap {m n : trunc_index} (X Y : pType)
  `{!IsConnected m.+1 X} `{!IsTrunc (n +2+ m).+1 Y}
  : IsTrunc n.+1 (X ->* Y).
Proof.
Admitted.

Global Instance contr_pmap_smash `{Funext} {n m : trunc_index} (X Y Z : pType)
  `{!IsConnected n.+1 X} `{!IsConnected m.+1 Y} `{!IsTrunc (n +2+ m).+1 Z}
  : Contr (Smash X Y ->* Z).
Proof.
  rapply (contr_equiv' _ (pequiv_pmap_uncurry _ _ _)).
  rapply contr_inhabited_hprop.
  exact (point _).
Defined.

(** Corollary 2.32: Connectivity of the smash product.  With different indexing, this says that for [n] and [m] natural numbers, [X] [n-1]-connected and [Y] [m-1]-connected, the smash product of [X] and [Y] is [n+m-1]-connected. *)
Corollary isconnected_smash `{Funext} {n m : trunc_index} (X Y : pType)
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
