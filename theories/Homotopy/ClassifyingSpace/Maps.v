(** * Mapping spaces between classifying spaces *)

From HoTT Require Import Basics Types.
Require Import Universes.HSet.
Require Import Truncations.Core Connectedness SeparatedTrunc.
Require Import Algebra.Groups.Group Subgroup Algebra.AbGroups.Centralizer.
Require Import Pointed WildCat WildCat.Core.
Require Import Homotopy.ClassifyingSpace.Core.
Require Import Colimits.Quotient GraphQuotient.
Require Import Cubical.PathSquare.
Require Import Homotopy.HomotopyGroup.
Export Homotopy.ClassifyingSpace.Core.ClassifyingSpaceNotation.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** ** Centralizers of general subtypes *)

(** The centralizer of the elements of [G] for which [H] holds. *)
Definition subtype_centralizer {G : Group} (H : G -> Type)
  : G -> Type
  (* Note the order of operations here.  We do this to match the original proofs for the centraliser of an element. *)
  := fun g => merely (forall h : G, H h -> centralizer h g).

Instance issubgroup_subtype_centralizer {G : Group} (H : G -> Type)
  : IsSubgroup (subtype_centralizer H).
Proof.
  srapply Build_IsSubgroup.
  - apply tr.
    intros h Hh.
    exact (centralizer_unit h).
  - intros x y cx cy.
    strip_truncations; apply tr.
    intros h Hh.
    exact (centralizer_sgop _ _ _ (cx h Hh) (cy h Hh)).
  - intros x Hx.
    strip_truncations; apply tr.
    intros h Hh.
    exact (centralizer_inverse h x (Hx h Hh)).
Defined.

Definition subtype_centralizer_subgroup
  {G : Group} (H : G -> Type)
  := Build_Subgroup G (subtype_centralizer H) _.

Definition grp_image_factorization {G H K : Group} (u : G $-> H) (v : H $-> K)
  : (v $o u) $== (grp_homo_restr v _) $o grp_homo_image_in u
  := fun x => idpath.

Definition grp_image_homotopic_grp_homo
  {G H : Group} {u v : G $-> H} (p : u $== v)
  : subgroup_group (grp_image u) $-> subgroup_group (grp_image v).
Proof.
  srapply subgroup_corec.
  - apply subgroup_incl.
  - intros [h uh].
    strip_truncations; apply tr.
    exact (uh.1; (p _)^ @ uh.2).
Defined.

Definition inv_grp_image_homotopic_grp_homo
  {G H : Group} {u v : G $-> H} (p : u $== v) (q : v $== u)
  : (grp_image_homotopic_grp_homo p) o (grp_image_homotopic_grp_homo q) == idmap.
Proof.
  intro x.
  apply path_sigma_hprop.
  reflexivity.
Defined.

Definition grp_iso_grp_image_homotopic_grp_homo
  {G H : Group} {u v : G $-> H} (p : u $== v)
  : subgroup_group (grp_image u) $<~> subgroup_group (grp_image v).
Proof.
  snapply Build_GroupIsomorphism.
  1: exact (grp_image_homotopic_grp_homo p).
  snapply isequiv_adjointify.
  1: exact (grp_image_homotopic_grp_homo (fun x => (p x)^)).
  1,2: by apply inv_grp_image_homotopic_grp_homo.
Defined.

Definition conj_grp_homo {G H : Group} (u v : G $-> H)
  := merely {h : H & forall g : G, u g = grp_conj h (v g)}.

Instance reflexive_conj_grp_homo {G H : Group}
  : Reflexive (conj_grp_homo (G:=G) (H:=H)).
Proof.
  intro u.
  apply tr.
  exists group_unit.
  intro g; exact (grp_conj_unit (u g))^.
Defined.

Instance symmetric_conj_grp_homo {G H : Group}
  : Symmetric (conj_grp_homo (G:=G) (H:=H)).
Proof.
  intros u v cuv.
  strip_truncations; apply tr.
  destruct cuv as [h ch].
  exists (inv h).
  intro g.
  rewrite (ch g).
  symmetry.
  napply grp_conj_inv_l.
Defined.

Instance transitive_conj_grp_homo {G H : Group}
  : Transitive (conj_grp_homo (G:=G) (H:=H)).
Proof.
  intros u v w cuv cvw.
  strip_truncations; apply tr.
  destruct cuv as [h1 ch1]; destruct cvw as [h2 ch2].
  exists (h1 * h2).
  intro g.
  lhs apply ch1.
  rewrite ch2.
  symmetry; napply grp_conj_op.
Defined.

Definition groupreps (G H : Group) : Type
  := @Quotient (G $-> H) (conj_grp_homo).

Definition idmap_fmap_grp_conj {G : Group} (g : G)
  : fmap B (grp_conj g) == idmap.
Proof.
  srapply ClassifyingSpace_ind_hset.
  - cbn. exact (bloop g).
  - intro x.
    rapply equiv_sq_dp^-1.
    snapply equiv_sq_path.
    rewrite ClassifyingSpace_rec_beta_bloop.
    rhs_V rapply bloop_pp.
    rewrite ap_idmap.
    lhs_V rapply bloop_pp.
    symmetry; exact (ap bloop (grp_inv_gV_g _ g)).
Defined.

(** ** Connected components of [B G -> B H] *)

Definition pi0_map_bg_groupreps `{ua : Univalence} (G H : Group)
  : groupreps G H -> Trunc 0 (B G -> B H).
Proof.
  srefine (Quotient_rec _ _ _ _); cbn beta.
  - intro f.
    apply tr.
    exact (fmap B f).
  - intros a b h.
    strip_truncations; destruct h as [h r].
    apply ap.
    apply path_forall.
    lhs' exact (fmap2 (g:=grp_conj h $o b) B r).
    lhs' exact (fmap_comp B b (grp_conj h)).
    intro x.
    exact (idmap_fmap_grp_conj h _).
Defined.

(** We first show that [pi0_map_bg_groupreps] is an embedding. *)
Definition isemb_pi0_map_bg_groupreps `{ua : Univalence} {G H : Group}
  : IsEmbedding (pi0_map_bg_groupreps G H).
Proof.
  apply isembedding_isinj_hset.
  rapply Quotient_ind2_hprop.
  intros u v p.
  srapply path_quotient.
  apply (equiv_path_Tr _ _)^-1 in p.
  strip_truncations; apply tr.
  pose (h := equiv_g_loops_bg^-1 (ap10 p bbase)).
  exists h.
  intro x.
  simpl.
  apply (equiv_inj equiv_g_loops_bg).
  simpl.
  rewrite 2 bloop_pp.
  rewrite bloop_inv.
  (* [h] is defined by applying [equiv_g_loops_bg^-1] and [bloop] is the inverse of that function. *)
  rewrite eisretr.
  rewrite <- 2 ap_fmap_b.
  exact (ap_homotopic (ap10 p) (bloop x)).
Defined.

Definition isemb_pi0_map_bg_groupreps `{ua : Univalence} {G H : Group}
  : IsEmbedding (pi0_map_bg_groupreps G H).
Proof.
  apply isembedding_isinj_hset.
  rapply Quotient_ind2_hprop.
  intros u v p.
  srapply path_quotient.
  exact (isinjective_pi0_map_bg_groupreps _ _ p).
Defined.

(** When [Y] is connected, every function [X -> Y] is merely pointed, so [pointed_fun] is a surjection. *)
Instance issurj_pointed_fun_conn `{Univalence} {X Y : pType} `{IsConnected 0 Y}
  : IsSurjection (pointed_fun : (X ->* Y) -> (X -> Y)).
Proof.
  apply (cancelR_issurjection (issig_pmap X Y)); cbn.
  rapply conn_map_pr1.
Defined.

(** It follows that [pi0_map_bg_groupreps] is surjective.  By definition, we have a commutative diagram
<<
               fmap B             pointed_fun
        G $-> H   <~>   (BG ->* BH)  ---------->  (BG -> BH)
           |                                      |
  class_of |                                      | tr
           v                                      v
        groupreps G H ------------------> Tr 0 (BG -> BH)
                     pi0_map_bg_groupreps
>>
    To show that [pi0_map_bg_groupreps] is surjective, it suffices to show that this is true after precomposition with [class_of] and so we just need to show that the other three maps are surjective.  Rocq can prove these by typeclass search, with one hint for [tr]. *)
Definition issurj_pi0_map_bg_groupreps `{ua : Univalence} {G H : Group}
  : IsSurjection (pi0_map_bg_groupreps G H).
Proof.
  apply (cancelR_issurjection (class_of _)).
  change (IsConnMap (Tr (-1)) (tr (n:=0) o pointed_fun o fmap (a:=G) (b:=H) B)).
  pose (@isconnmap_pred' 0). (* [tr] is in fact 0-connected, so we give this hint. *)
  exact _.
Defined.

Instance isequiv_pi0_map_bg_groupreps `{ua : Univalence} (G H : Group)
  : IsEquiv (pi0_map_bg_groupreps G H).
Proof.
  apply isequiv_surj_emb.
  - exact issurj_pi0_map_bg_groupreps.
  - exact isemb_pi0_map_bg_groupreps.
Defined.

Definition equiv_groupreps_pi0_map_bg `{ua : Univalence} (G H : Group)
  : (groupreps G H) <~> Pi 0 [B G -> B H, fun x => bbase]
  := Build_Equiv _ _ _ (isequiv_pi0_map_bg_groupreps G H).

(** ** The fundamental group of [B G -> B H] *)

Definition ClassifyingSpace_rec2_beta_bloop1_bbase {G H : Group}
  (P : Type) `{IsTrunc 1 P} (bbase' : P)
  (bloop1 : G -> bbase' = bbase')
  (bloop1_pp : forall x y : G, bloop1 (x * y) = bloop1 x @ bloop1 y)
  (bloop2 : H -> bbase' = bbase')
  (bloop2_pp : forall x y : H, bloop2 (x * y) = bloop2 x @ bloop2 y)
  (bloop_comm : forall g h, bloop1 g @ bloop2 h = bloop2 h @ bloop1 g)
  (g : G)
  : ap10 (ap (ClassifyingSpace_rec2 P bbase' bloop1 bloop1_pp bloop2 bloop2_pp bloop_comm)
          (bloop g))
      bbase = bloop1 g.
Proof.
  lhs_V napply ap_apply_Fl.
  unfold ClassifyingSpace_rec2, ClassifyingSpace_rec_forall; cbn.
  rapply ClassifyingSpace_rec_beta_bloop.
Defined.

Definition map_bg_b_centralizer_grp_image {G H : Group} (v : G $-> H)
  : B (subtype_centralizer_subgroup (grp_image v)) -> (B G -> B H).
Proof.
  napply (fmap11_B (subgroup_incl _) v).
  intros [h ch] g; cbn.
  symmetry.
  strip_truncations.
  exact (ch (v g) (tr (g; idpath))).
Defined.

Definition loops_map_bg_centralizer_grp_image {G H : Group} (v : G $-> H)
  : subtype_centralizer_subgroup (grp_image v)
      -> loops [B G -> B H, fmap B v]
  := fun x => ap (map_bg_b_centralizer_grp_image v) (bloop x).

Definition pi1_map_bg_centralizer_grp_image {G H : Group} (v : G $-> H)
  : subtype_centralizer_subgroup (grp_image v)
      -> Pi 1 [B G -> B H, fmap B v]
  := tr o (loops_map_bg_centralizer_grp_image v).

Definition centralizer_grp_image_pi1_map_bg `{ua : Univalence}
  {G H : Group} (v : G $-> H)
  : Pi 1 [B G -> B H, fmap B v]
    $-> subtype_centralizer_subgroup (grp_image v).
Proof.
  (* It's enough to define a group homomorphism to [H] whose image is in the centralizer. *)
  snapply subgroup_corec.
  - refine (_^-1$ $o _).
    (* For the homomorphism to [H], it's enough to define a homomorphism to [LoopGroup (B H)]. *)
    1: exact grp_iso_g_loopgroup_bg.
    (* And for that, [ap10] does the trick. *)
    snapply Build_GroupHomomorphism.
    + intro p.
      strip_truncations; change (pointed_fun (fmap B v) = (fmap B v)) in p.
      exact (ap10 p bbase).
    + intros p q.
      strip_truncations; change (pointed_fun (fmap B v) = fmap B v) in p, q.
      cbn.
      exact (ap10_pp p q bbase).
  (* Now we need to show that the image of our homomorphism is in the centralizer. *)
  - intro p.
    strip_truncations; change (pointed_fun (fmap B v) = (fmap B v)) in p.
    cbn.
    apply tr.
    intros h sh.
    snapply (centralizer_iso grp_iso_g_loopgroup_bg); cbn.
    rewrite (eisretr bloop).
    strip_truncations.
    destruct sh as [g []]; clear h.
    rewrite <- ap_fmap_b.
    unfold centralizer.
    cbn; napply concat_Ap.
Defined.

Instance isequiv_centralizer_grp_image_pi1_map_bg `{ua : Univalence}
  {G H : Group} (v : G $-> H)
  : IsEquiv (centralizer_grp_image_pi1_map_bg v).
Proof.
  srapply isequiv_adjointify.
  - exact (pi1_map_bg_centralizer_grp_image v).
  - intros [h ch]; strip_truncations.
    apply path_sigma_hprop; cbn.
    apply moveR_equiv_V.
    napply ClassifyingSpace_rec2_beta_bloop1_bbase.
  - intro u.
    strip_truncations.
    change (pointed_fun (fmap B v) = (fmap B v)) in u.
    unfold pi1_map_bg_centralizer_grp_image.
    apply ap.
    unfold loops_map_bg_centralizer_grp_image.
    apply (equiv_inj ap10).
    apply path_forall.
    rapply ClassifyingSpace_ind_hprop.
    lhs napply ClassifyingSpace_rec2_beta_bloop1_bbase.
    cbn.
    apply eisretr.
Defined.

Definition equiv_pi1_map_bg_centralizer_grp_image `{ua : Univalence}
  {G H : Group} (v : G $-> H)
  : GroupIsomorphism
    (Pi 1 [B G -> B H, fmap B v])
    (subtype_centralizer_subgroup (grp_image v))
  := Build_GroupIsomorphism _ _ _ (isequiv_centralizer_grp_image_pi1_map_bg v).
    (Pi 1 [B G -> B H, fmap B f])
    (subtype_centralizer_subgroup (grp_image f))
  := Build_GroupIsomorphism _ _ _ (isequiv_centralizer_grp_image_pi1_map_bg f).

Definition pi0_map_bg_groupreps_pi1 `{Univalence}
  (X : pType) (G : Group) `{IsConnected 0 X}
  : groupreps (Pi 1 X) G <~> Tr 0 (X -> B G).
Proof.
  refine (Trunc_functor_equiv 0 (equiv_map_bg X G) oE _).
  srapply equiv_groupreps_pi0_map_bg.
Defined.

Definition pi1_map_bg_groupreps_pi1 `{Univalence}
  (X : pType) (G : Group) `{IsConnected 0 X} (v : Pi 1 X $-> G)
  : GroupIsomorphism
      (Pi 1 [X -> B G, equiv_bg_pi1_adjoint X G v])
      (subtype_centralizer_subgroup (grp_image v)).
Proof.
  refine (grp_iso_compose (equiv_pi1_map_bg_centralizer_grp_image v) _).
  srapply groupiso_pi_functor.
  symmetry.
  srapply Build_pEquiv'.
  - exact (equiv_map_bg X G).
  - unfold "pt".
    unfold ispointed_type.
    reflexivity.
Defined.
