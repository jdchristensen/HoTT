(* These things should probably be moved to Homotopy/Smash.v. *)
(* Also, there's a typo there:  smash_rec_beta_gluer should be capitalized. *)

Require Import Basics Types.
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

Lemma pmap_uncurry `{Funext} (X Y Z : pType)
  : (X ->** (Y ->** Z)) ->* (Smash X Y ->** Z).
Proof.
  snrapply Build_pMap.
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
Defined.

(** These facts are taken as axioms for now. *)
Local Lemma sect1 `{Funext} (X Y Z : pType)
  : Sect (nested_pprecompose Z (psm X Y)) (pmap_uncurry X Y Z).
Admitted.

Local Lemma sect2 `{Funext} (X Y Z : pType)
  : Sect (pmap_uncurry X Y Z) (nested_pprecompose Z (psm X Y)).
Admitted.

Global Instance isequiv_pmap_uncurry `{Funext} (X Y Z : pType)
  : IsEquiv (pmap_uncurry X Y Z).
Proof.
  snrapply isequiv_adjointify.
  - exact (nested_pprecompose Z (psm X Y)).
  - apply sect1.
  - apply sect2.
Defined.

(** Lemma 2.31 [van Doorn, Theorem 4.3.28] *)
(** We define the maps, but take it as axioms that they are inverse to each other. *)
(** For now, no naturality conditions, just an equivalence. *)
Definition pequiv_pmap_uncurry `{Funext} (X Y Z : pType)
  : (X ->** (Y ->** Z)) <~>* (Smash X Y ->** Z)
  := Build_pEquiv _ _ (pmap_uncurry X Y Z) _.

(** This is one of the three naturality properties of [pmap_uncurry]. *)
(* We eventually will need a pointed homotopy, but for now we just claim an unpointed one. *)
Definition pmap_uncurry_nat_X `{Funext} (X X' Y Z : pType) (f : X ->* X')
  : pmap_uncurry X Y Z o* pprecompose (Y ->** Z) f ==
    pprecompose Z (Smash_functor f pmap_idmap) o* pmap_uncurry X' Y Z.
Proof.
  intro g.
  unfold pequiv_pmap_uncurry, pointed_equiv_fun.
  apply path_pforall.
  snrapply Build_pHomotopy.
  - snrapply Smash_ind.
    + intros x y.
      lazy.  reflexivity.
    + lazy.  reflexivity.
    + lazy.  reflexivity.
    + intro x.  cbn beta.
      snrapply equiv_dp_paths_FlFr.
      rewrite concat_p1.
      apply moveR_Vp.
      refine (_ @ (concat_p1 _)^).
      unfold pprecompose, "o*", Build_pMap, pointed_fun.
      refine (ap_compose _ _ _ @ _).
      rewrite 2 Smash_rec_beta_gluel.
      change (ap (sm (f x)) (point_eq pmap_idmap)) with (idpath (sm (f x) (point Y))).
      rewrite concat_1p.
      rapply Smash_rec_beta_gluel.
    + intro y.  cbn beta.
      snrapply equiv_dp_paths_FlFr.
      rewrite concat_p1.
      apply moveR_Vp.
      refine (_ @ (concat_p1 _)^).
      unfold pprecompose, "o*", Build_pMap, pointed_fun.
      refine (ap_compose _ _ _ @ _).
      rewrite 2 smash_rec_beta_gluer.
      unfold pmap_idmap, Build_pMap, pointed_fun.
      pointed_reduce_pmap f.
      rewrite 2 concat_1p.
      rapply smash_rec_beta_gluer.
  - simpl.
    pointed_reduce_pmap f.
    rewrite concat_1p.
    symmetry; apply concat_pV.
Defined.

(** Lemma 2.27 [Buchholtz-van Doorn-Rijke, Corollary 4.3] *)
(** We take this as an axiom. *)
Global Instance istrunc_ppmap {m n : trunc_index} (X Y : pType)
  `{!IsConnected m.+1 X} `{!IsTrunc (n +2+ m).+1 Y}
  : IsTrunc n.+1 (X ->* Y).
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

(** TODO: Make this much more efficient. *)
Lemma equiv_isequiv_ppmap_compose_isequiv_compose `{Funext} {A B : pType} (f : A ->* B) (Z : Type)
  : (forall (z : Z), IsEquiv (fun g : B ->* Build_pType Z z => g o* f : A ->* Build_pType Z z))
  <~> IsEquiv (fun g : B -> Z => g o f : A -> Z).
Proof.
  srapply equiv_iff_hprop.
  { intro K.
    pose (@isequiv_functor_sigma Z (fun z => B ->* Build_pType Z z) Z (fun z => A ->* Build_pType Z z)
      idmap _ (fun z => (fun g : B ->* Build_pType Z z => g o* f : A ->* Build_pType Z z)) _) as isT.
    srefine (@isequiv_commsq _ _ _ _ _ _ _ _ _ isT _ _).
    1: intros [z g] b; exact (g b).
    1: intros [z g] a; exact (g a).
    1: reflexivity.
    { snrapply isequiv_adjointify.
      { intro g; eexists.
        exact (pmap_from_point g (point _)). }
      1: cbn; reflexivity.
      { intros [z g].
        srapply path_sigma.
        1: exact (point_eq g).
        pointed_reduce.
        reflexivity. } }
    snrapply isequiv_adjointify.
    { intro g; eexists.
      exact (pmap_from_point g (point _)). }
    1: cbn; reflexivity.
    { intros [z g].
      srapply path_sigma.
      1: exact (point_eq g).
      pointed_reduce.
      reflexivity. } }
  intro K.
  rapply isequiv_from_functor_sigma.
  srefine (@isequiv_commsq' _ _ _ _ _ _ _ _ _ K _ _).
  1: intros [z g] b; exact (g b).
  1: intros [z g] a; exact (g a).
  1: reflexivity.
  { snrapply isequiv_adjointify.
    { intro g; eexists.
      exact (pmap_from_point g (point _)). }
    1: cbn; reflexivity.
    { intros [z g].
      srapply path_sigma.
      1: exact (point_eq g).
      pointed_reduce.
      reflexivity. } }
  snrapply isequiv_adjointify.
  { intro g; eexists.
    exact (pmap_from_point g (point _)). }
  1: cbn; reflexivity.
  { intros [z g].
    srapply path_sigma.
    1: exact (point_eq g).
    pointed_reduce.
    reflexivity. }
Defined.

Lemma O_inverts_from_isequiv_pmap_precomp {O : ReflectiveSubuniverse} `{Funext} {A B : pType} (f : A ->* B)
  : (forall Z : Type, In O Z -> forall z : Z, IsEquiv (fun g : B ->* {| pointed_type := Z; ispointed_type := z |} => g o* f)) -> O_inverts O f.
Proof.
  intro K.
  nrapply O_inverts_from_isequiv_precompose; [exact _|].
  intros Z inZ.
  rapply equiv_isequiv_ppmap_compose_isequiv_compose.
Defined.

(** TODO: give better name *)
Lemma isequiv_pmap_precomp_smash_ptr_idmap `{Funext} (n m : trunc_index) (X Y T : pType) `{!IsTrunc (m +2+ n).+1 T} `{!IsConnected n.+1 X}
  : IsEquiv (fun (f : Smash (pTr m.+1 Y) X ->* T) => f o* (Smash_functor ptr pmap_idmap) : Smash Y X ->* T).
Proof.
  snrapply isequiv_commsq.
  8,9: rapply (pointed_isequiv _ _ (pequiv_pmap_uncurry _ _ _)).
  1: intros g; exact (g o* ptr).
  1: rapply pmap_uncurry_nat_X.
  snrapply (isequiv_commsq (@equiv_ptr_rec _ m.+1 Y (X ->** T) _)).
  3,4: exact idmap.
  1,4,5,6: exact _.
  1: rapply (@istrunc_ppmap n m X T).
  reflexivity.
Defined.

(** Lemma 2.42 *)
Global Instance isequiv_ptr_smash_functor `{Funext} {n m : trunc_index} (X Y : pType)
  `{!IsConnected n.+1 X}
  : IsEquiv (ptr_functor (m +2+ n).+1 (Smash_functor (ptr (n:=m.+1) (A:=Y)) (@pmap_idmap X))).
Proof.
  snrapply O_inverts_from_isequiv_pmap_precomp.
  1: exact _. (* Funext. *)
  intros Z inZ z.
  srapply (isequiv_pmap_precomp_smash_ptr_idmap n m).
Defined.
