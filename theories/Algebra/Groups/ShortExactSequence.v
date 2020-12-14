Require Import Basics Types WildCat Pointed HSet HFiber.
Require Import Groups.Group Groups.Subgroup Groups.Kernel Groups.GrpPullback.
Require Import Homotopy.ExactSequence Modalities.Identity.
Require Import Spaces.Finite Limits.Pullback.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.
Local Open Scope path_scope.

(** * Complexes of groups *)

Proposition grp_homo_cxfib {A B C : Group} {i : A $-> B} {f : B $-> C} (cx : IsComplex i f)
  : GroupHomomorphism A (grp_kernel f).
Proof.
  destruct cx as [phi eq]; simpl in phi, eq.
  exact (@grp_kernel_corec _ _ _ f i phi).
Defined.

Definition grp_iscomplex_trivial_l {Z X Y : Group} (f : X $-> Y)
  : IsComplex (@grp_homo_const Z X) f.
Proof.
  srapply Build_pHomotopy.
  - intro x; cbn.
    exact (grp_homo_unit f).
  - apply path_ishprop.
Defined.

Definition grp_iscomplex_trivial_r {X Y Z : Group} (f : X $-> Y)
  : IsComplex f (@grp_homo_const Y Z).
Proof.
  srapply Build_pHomotopy.
  - intro x; reflexivity.
  - apply path_ishprop.
Defined.

Local Existing Instance ishprop_phomotopy_hset.
Local Existing Instance ishprop_isexact_hset.

(** For a pointed set Y and a function f : X -> Y, the projection map from the fibre to X is an embedding. *)
(* jarlg: This is mapinO_pr1, with some juggling. Can't be placed in HSet.v or HFiber.v due to dependencies. Could be inlined using rapply, but that takes a second to resolve. So a lemma seems justified, but where should it be placed? *)
Lemma isembedding_pr1_hset `{Funext} {X Y : hSet} (f : X -> Y) (y : Y)
  : IsEmbedding (pr1 : hfiber f y -> X).
Proof.
  (* jarlg: rapply here works, but it's faster to give the whole proof. *)
  nrapply (snd (iff_forall_inO_mapinO_pr1 (Tr (-1)) _)).
  apply mapinO_pr1.
  exact inO_hfiber_ino_map.
Defined.

(* jarlg: Changed to (-1)-exactness from pure exactness since it's what I want to use in practice. I didn't find converting from pure exactness to (-1)-exactness easy inline (or even as a standalone proof). *)
(** For K -> A constant, a complex K -> A -> B of groups is (-1)-exact if and only if the map A -> B is an embedding. *)
Lemma equiv_grp_isexact_isembedding `{Univalence} {K A B : Group} (f : A $-> B)
  : IsExact (Tr (-1)) (@grp_homo_const K A) f <~> IsEmbedding f.
Proof.
  srapply equiv_iff_hprop.
  - intros [cx conn] b a.
    rapply (transport IsHProp (x:= hfiber f 0)).
    + apply path_universe_uncurried; symmetry.
      apply equiv_grp_hfiber.
      exact a; clear a.
    + apply hprop_allpath.
      intros x y.
      assert (u : Tr (-1) (hfiber (cxfib cx) x)) by apply (conn x).
      assert (v : Tr (-1) (hfiber (cxfib cx) y)) by apply (conn y).
      strip_truncations. (* jarlg: Slightly slow, would be good to avoid. *)
      refine (u.2^ @ _ @ v.2).
      apply (isinj_embedding pr1).
      * apply isembedding_pr1_hset.
      * reflexivity.
  - intro isemb_f.
    exists (grp_iscomplex_trivial_l f).
    intros y; rapply contr_inhabited_hprop.
    apply tr.
    exists mon_unit; apply path_ishprop.
Defined.

Corollary equiv_grp_isexact_kernel `{Univalence} {K A B : Group} (f : A $-> B)
  : IsExact (Tr (-1)) (@grp_homo_const K A) f
            <~> (grp_kernel f = trivial_subgroup).
Proof.
  exact ((equiv_kernel_isembedding f)^-1%equiv oE equiv_grp_isexact_isembedding f).
Defined.

(** For B -> K' constant, a complex A -> B -> K' of groups is (-1)-exact if and only if the map A -> B is a surjection. *)
Lemma equiv_grp_isexact_issurjection `{Univalence} {A B K' : Group} (f : A $-> B)
  : IsExact (Tr (-1)) f (@grp_homo_const B K') <~> IsSurjection f.
Proof.
  apply equiv_iff_hprop.
  - intros [cx conn] b.
    unfold IsConnMap in conn.
    apply (transport (IsConnected (Tr (-1))) (x := hfiber (cxfib cx) (b; 1))).
    + apply path_universe_uncurried.
      srefine (equiv_hfiber_embedding pr1 (b; idpath)).
      apply isembedding_pr1_hset.
    + exact (conn (b; idpath)).
  - intro conn_f.
    exists (grp_iscomplex_trivial_r f); cbn.
    intro b.
    apply (@transport _ Contr (Tr (-1) (hfiber f b.1)) (Tr (-1) (hfiber (fun x:A => (f x; idpath)) b))).
    + apply (ap (Tr (-1))).
      apply path_universe_uncurried; symmetry.
      refine (equiv_hfiber_embedding pr1 b).
      apply isembedding_pr1_hset.
    + apply conn_f.
Defined.
