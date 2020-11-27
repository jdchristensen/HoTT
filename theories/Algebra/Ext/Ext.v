Require Import Basics Types WildCat Pointed.
Require Import Algebra.AbGroups Homotopy.ExactSequence Modalities.Identity.


Local Open Scope mc_scope.
Local Open Scope mc_add_scope.
Local Open Scope path_scope.


Proposition grp_homo_cxfib {A B C : Group} {i : A $-> B} {f : B $-> C} (cx : IsComplex i f)
  : GroupHomomorphism A (grp_kernel f).
Proof.
  destruct cx as [phi eq]; simpl in phi, eq.
  exact (@grp_kernel_corec _ _ _ f i phi).
Defined.

(* jarlg: Maybe this can be deduced from iscomplex_trivial, but I didn't manage.*)
Definition grp_iscomplex_trivial {X Y : Group} (f : X $-> Y)
  : IsComplex (@grp_homo_const grp_trivial X) f.
Proof.
  srapply Build_pHomotopy.
  - intro x; cbn.
    exact (grp_homo_unit f).
  - apply path_ishprop.
Defined.

Local Existing Instance ishprop_phomotopy_hset.
Local Existing Instance isequiv_purely_conn.
Local Existing Instance ishprop_isexact_hset.

(** The complex 0 -> A -> B is purely exact if and only if f is a group embedding. *)
Lemma equiv_grp_isexact_isembedding `{Univalence} {A B : Group} (f : A $-> B)
  : IsExact purely (@grp_homo_const grp_trivial A) f <~> IsEmbedding f.
Proof.
  srapply equiv_iff_hprop.
  - intros [cx conn] b a.
    rapply (transport IsHProp (x:= hfiber f 0)).
    + apply path_universe_uncurried; symmetry.
      apply equiv_grp_hfiber.
      exact a.
    + rapply (transport IsHProp (x:= grp_trivial)).
      apply path_universe_uncurried.
      rapply Build_Equiv.
  - intro isemb_f.
    exists (grp_iscomplex_trivial f).
    intros y; rapply contr_inhabited_hprop.
    exists tt; apply path_ishprop.
Defined.

(** The complex 0 -> A -> B is purely exact if and only if the kernel of f is trivial. *)
Corollary equiv_grp_isexact_kernel `{Univalence} {A B : Group} (f : A $-> B)
  : IsExact purely (@grp_homo_const grp_trivial A) f
            <~> (grp_kernel f = trivial_subgroup).
Proof.
  exact ((equiv_kernel_isembedding f)^-1%equiv oE equiv_grp_isexact_isembedding f).
Defined.
