Require Import Basics Types WildCat Pointed HSet HFiber.
Require Import Groups.Group Groups.Subgroup Groups.Kernel Groups.GrpPullback.
Require Import Homotopy.ExactSequence Modalities.Identity Modalities.ReflectiveSubuniverse.
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

(** For B -> C constant, a complex A -> B -> C of groups is (-1)-exact if and only if the map A -> B is a surjection. *)
Lemma equiv_grp_isexact_issurjection `{Univalence} {A B C : Group} (f : A $-> B)
  : IsExact (Tr (-1)) f (@grp_homo_const B C) <~> IsSurjection f.
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

(** * Short exact sequences *)

Local Open Scope nat_scope.

(* jarlg: Could this notation be improved? Should we enable it in Spaces.Finite and import it from there? *)
Local Notation "n .+1" := (fsucc n).
Local Notation "n .+0" := (fin_incl n) (at level 0).
Local Notation "[ n ]" := (fin_nat n).

(* jarlg: A short exact sequence is indexed by Fin 5 (five elements), and the setup could be generalized to length-n exact sequences by indexing with Fin n appropriately. Could do a general definition of "nExactSequence" which specializes to this for n=5 (or n=3 if you only count non-contractible types). Before considering that however, this definition should be usable. The proof of ses_pb below is the first testing ground. *)
Record ShortExactSequence : Type :=
{
  ses_carrier : Fin 5 -> Group;
  ses_end : Contr (ses_carrier [0]);
  ses_start : Contr (ses_carrier [4]);
  ses_fn : forall n : Fin 4, ses_carrier n.+1 $-> ses_carrier n.+0;
  ses_isexact : forall n : Fin 3, IsExact (Tr (-1)) (ses_fn n.+1) (ses_fn n.+0)
}.

Definition Build_ses_carrier (Z A B C Z' : Group) `{Contr Z} `{Contr Z'}
  : Fin 5 -> Group.
Proof.
  FinInd.
  - exact Z.
  - exact C.
  - exact B.
  - exact A.
  - exact Z'.
Defined.

Definition ses_index (n : Fin 3) (S : ShortExactSequence) : Group := ses_carrier S n.+1.+0.

Definition ses_A (S : ShortExactSequence) : Group := ses_carrier S [3].
Definition ses_B (S : ShortExactSequence) : Group := ses_carrier S [2].
Definition ses_C (S : ShortExactSequence) : Group := ses_carrier S [1].

Definition ses_i (S : ShortExactSequence) : ses_A S $-> ses_B S := ses_fn S [2].
Definition ses_p (S : ShortExactSequence) : ses_B S $-> ses_C S := ses_fn S [1].

Definition ses_cx_B (S : ShortExactSequence) : ses_p S $o ses_i S == grp_homo_const.
Proof.
  pose (E := (ses_isexact S [1])); exact cx_isexact.
Defined.

Definition Build_SES `{Univalence} {Z A B C Z' : Group} `{Contr Z} `{Contr Z'}
           (i : A $-> B) (p : B $-> C) `{IsEmbedding i} `{IsSurjection p} {E : IsExact (Tr (-1)) i p}
  : ShortExactSequence.
Proof.
  srapply Build_ShortExactSequence.
  1: exact (Build_ses_carrier Z A B C Z').
  1,2: exact _.
  - FinInd.
    1,4: apply grp_homo_const.
    + exact p.
    + exact i.
  - FinInd; cbn.
    + rapply (equiv_grp_isexact_issurjection p)^-1%equiv.
    + exact E.
    + rapply (equiv_grp_isexact_isembedding i)^-1%equiv.
Defined.

Lemma ses_pb `{Univalence} {C : Group} (S : ShortExactSequence) (phi : C $-> ses_C S)
  : ShortExactSequence.
Proof.
  pose (B' := grp_pullback (ses_p S) phi).

  snrapply (Build_SES (Z:=ses_carrier S [4]) (Z':=ses_carrier S [0])
                   (B:=grp_pullback (ses_p S) phi)
                   (grp_pullback_corec _ _ (ses_i S) grp_homo_const _)
                   (grp_pullback_pr2 (ses_p S) phi)).
  - exact H.
  - exact (ses_start S).
  - exact (ses_end S).
  - intro x; exact (ses_cx_B S x @ (grp_homo_unit phi)^).

  (** The corec-induced map into the pullback is an embedding, since (ses_i S) is one. *)
  - rapply isembedding_pullback_corec_embedding.
    apply (equiv_grp_isexact_isembedding (K:=ses_carrier S [4])).
    apply (transport (fun f => IsExact (Tr (-1)) f (ses_i S)) (x:=ses_fn S [3])).

    (* jarlg: How to do this bullet nicely? *)
    + pose (c := ses_start S).
      assert (c' : Contr (ses_carrier S [4] ->* ses_carrier S [3])) by apply contr_pmap_from_contr.
      apply path_contr.

    + exact (ses_isexact S [2]).

  (** The pullback of the surjection (ses_p S) along phi is a surjection. *)
  - rapply conn_map_pullback'.
    apply (equiv_grp_isexact_issurjection (C:=ses_carrier S [0])).
    apply (transport (fun f => IsExact (Tr (-1)) (ses_p S) f) (x:=ses_fn S [0])).

    + apply path_pforall.
      srapply Build_pHomotopy.
      * intro x; apply (path_contr (Contr0 := ses_end S)).
      * apply path_ishprop.
    + exact (ses_isexact S [0]).

  (** Transfering exactness to the pullback. *)
  - snrapply Build_IsExact.
    + srapply Build_pHomotopy.
      * reflexivity.
      * apply path_ishprop.

    + intros [b' p]; cbn.
      rapply contr_inhabited_hprop.
      pose (bf := (grp_pullback_pr1 _ _ b'; ((pullback_commsq (ses_p S) phi) b' @ ap phi p @ grp_homo_unit phi)) : pfiber (ses_p S)).
      pose proof (@center _ (conn_map_isexact (IsExact:=ses_isexact S [1]) bf)) as y.
      strip_truncations.
      destruct y as [y q].
      apply tr.
      exists y.

      nrapply equiv_path_sigma_hprop.

      * intro a.
        unfold ispointed_group. (* jarlg: Why is this necessary? *)
        exact _. (* jarlg: What is this finding? *)

      * apply equiv_path_sigma.
        exists (ap pr1 q).
        refine (transport_sigma' _ _@ _); cbn.
        apply equiv_path_sigma; cbn.
        exists p^; apply path_ishprop.

        Unshelve. (* jarlg: Can this be avoided? *)
        all: exact _.
Defined.
