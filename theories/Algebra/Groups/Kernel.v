Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import Algebra.Groups.Subgroup.
Require Import WildCat.

(** * Kernels of group homomorphisms *)

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Definition grp_kernel {A B : Group} (f : GroupHomomorphism A B) : Subgroup A.
Proof.
  snrapply Build_Subgroup.
  { srapply (Build_Group (hfiber f group_unit)); repeat split.
    - (** Operation *)
      intros [a p] [b q].
      exists (sg_op a b).
      rewrite grp_homo_op, p, q.
      apply left_identity.
    - (** Unit *)
      exists mon_unit.
      apply (grp_homo_unit f).
    - (** Inverse *)
      intros [a p].
      exists (-a).
      rewrite grp_homo_inv, p.
      exact negate_mon_unit.
    - (** HSet *)
      exact _.
    - (** Associativity *)
      intros [a p] [b q] [c r].
      srapply path_sigma_hprop.
      cbn; apply associativity.
    - (** Left identity *)
      intros [a p].
      srapply path_sigma_hprop.
      cbn; apply left_identity.
    - (** Right identity *)
      intros [a p].
      srapply path_sigma_hprop.
      cbn; apply right_identity.
    - (** Left inverse *)
      intros [a p].
      srapply path_sigma_hprop.
      cbn; apply left_inverse.
    - (** Right inverse *)
      intros [a p].
      srapply path_sigma_hprop.
      cbn; apply right_inverse. }
  (** The kernel is a subgroup of the source of the map *)
  snrapply Build_IsSubgroup.
  { snrapply Build_GroupHomomorphism.
    1: exact pr1.
    intros ??; reflexivity. }
  hnf; cbn; intros x y p.
  by apply path_sigma_hprop.
Defined.

Global Instance isnormal_kernel {A B : Group} (f : GroupHomomorphism A B)
  : IsNormalSubgroup (grp_kernel f).
Proof.
  apply isnormalsubgroup_of_cong_mem.
  intros g n.
  srefine ((_ ; _ ); _).
  3: reflexivity.
  simpl.
  rewrite grp_homo_op, grp_homo_op, grp_homo_inv.
  rewrite (pr2 n), (right_identity (- f g)).
  rewrite (negate_l _).
  reflexivity.
Defined.


(** ** Corecursion principle for group kernels *)

Proposition grp_kernel_corec {A B G : Group} {f : A $-> B} {g : G $-> A}
            (h : f $o g == grp_homo_const) : G $-> grp_kernel f.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact (fun x:G => (g x; h x)).
  - intros x x'.
    apply equiv_path_sigma_hprop; cbn.
    exact (grp_homo_op _ _ _).
Defined.

Theorem equiv_grp_kernel_corec `{Funext} {A B G : Group} {f : A $-> B}
  : (G $-> grp_kernel f) <~> (exists g : G $-> A, f $o g = grp_homo_const).
Proof.
  srapply Build_Equiv.
  - intro k; refine (subgrp_incl _ _ $o k; _).
    srapply equiv_path_grouphomomorphism; intro x; cbn.
    exact (k x).2.
  - srapply isequiv_adjointify.
    + intros [g p].
      exact (grp_kernel_corec (equiv_path_grouphomomorphism^-1%equiv p)).
    + intros [g p].
      apply equiv_path_sigma_hprop.
      apply equiv_path_grouphomomorphism; intro; reflexivity.
    + intro k.
      apply equiv_path_grouphomomorphism; intro x.
      apply equiv_path_sigma_hprop; reflexivity.
Defined.


(** ** Characterization of group embeddings *)

Local Existing Instance ishprop_path_trivial.

Proposition equiv_kernel_isembedding `{Univalence} {A B : Group} (f : A $-> B)
  : (grp_kernel f = subgrp_trivial) <~> IsEmbedding f.
Proof.
  srapply Build_Equiv.
  - intros phi b; unfold hfiber.
    apply ishprop_sigma_disjoint.
    intros a a' p q.
    rewrite <- q in p.
    pose (P := ap (fun g => g *  -(f a')) p); cbn in P.
    rewrite right_inverse in P.
    rewrite <- (grp_homo_inv f) in P.
    rewrite <- (grp_homo_op f) in P.
    apply (group_cancelR (- a')).
    refine (_ @ (right_inverse a')^).
    pose (z := (a * -a'; P) : grp_kernel f).
    change (a * -a') with (pr1 z).
    pose (m := (mon_unit; grp_homo_unit f) : grp_kernel f).
    change mon_unit with (pr1 m).
    apply (ap pr1).
    apply (equiv_ap' (equiv_path _ _ (ap (@group_type o (subgroup_group A)) phi))).
    apply path_ishprop.
  - srapply isequiv_adjointify.
    { unfold IsEmbedding.
      intro isemb_f.
      srapply equiv_path_subgroup.
      srefine (grp_iso_inverse _; _).
      * srapply Build_GroupIsomorphism.
        -- exact grp_homo_const.
        -- srapply isequiv_adjointify.
           1: exact grp_homo_const.
           all: intro x; apply path_ishprop.
      * apply equiv_path_grouphomomorphism; intro x; cbn.
        refine (ap pr1 _ @ _).
        -- apply path_ishprop.
        -- exact (idpath (pr1 (mon_unit A; grp_homo_unit f))). }
    all: intro; apply path_ishprop.
Defined.
