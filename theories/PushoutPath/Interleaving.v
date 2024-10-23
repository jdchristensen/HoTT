Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.Cocone.
Require Import Diagrams.Sequence.
Require Import WildCat.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Diagram.
Require Import Types.

Locate Is1Cat_Strong.


(** Suppose we have sequences A_i and B_i. An interleaving from 
    A_i to B_i consists of two natural transformations
    d : A_i => B_i (d for down) and u : B_i => A_i+1 (u for up), 
    such that the composites (u o d) and (d o i) corresponds to 
    the morphisms in the diagram itself. In other words,
    the following diagram is commutative: 
    
    A_0 -------> A_1 ------> A_2 ------>
        \        ^  \        ^ 
         \      /    \      /  
          \    /      \    /         ...
           v  /        v  /
           B_0 ------> B_1 ------->
    
    Given the setup above, we want to say that the colimit of the 
    upper lower sequences are the same. *)

(** From a sequence A, we can produce a diagram map from [A] to [succ_seq A]. 
    It's the map that applies the arrow in the sequence to every element. *)

Definition seq_to_succ_seq (A : Sequence) : DiagramMap A (succ_seq A).
Proof.
  snrapply Build_DiagramMap.
  - intros n a. exact a^+. 
  - intros m n [] x. reflexivity.
Defined.

(** Given a map of sequences we can define a map between 
    their succesor sequences. *)

Definition succ_seq_map_seq_map {A B : Sequence} (f : DiagramMap A B) 
  : DiagramMap (succ_seq A) (succ_seq B).
Proof.
 snrapply Build_DiagramMap.
 - intros n a. exact (f (S n) a).
 - intros m n [] a. exact (DiagramMap_comm f _ a).
Defined.

(** Cocones over a sequence defines a cocone over the successor sequence *)

Definition succ_seq_cocone_seq_cocone {A : Sequence} (T : Type) (C : Cocone A T)
  : Cocone (succ_seq A) T.
Proof.
  srapply Build_Cocone.
  - intros n a. exact (C (S n) a).
  - intros m n [] a. rapply (legs_comm C).
Defined.

(** [cocone_precompose (seq_to_succ_seq A)] is an equivalence *)

Definition isequiv_cocone_precompose_seq_to_succ_seq
  `{Funext} {A : Sequence} {X : Type} 
  : IsEquiv (cocone_precompose (seq_to_succ_seq A) (X:= X)).
Proof.
  snrapply isequiv_adjointify.
  - exact (succ_seq_cocone_seq_cocone X).
  - intro C.
    srapply path_cocone.
    + intros n a. simpl. exact (legs_comm C n _ idpath a).
    + intros m n [] a. simpl.
      snrapply (ap (fun x => x @ _) (concat_1p _)).
  - intro C.
    srapply path_cocone.
    + intros n a. simpl. exact (legs_comm C n _ idpath a).
    + intros m n [] a. simpl.
      snrapply (ap (fun x => x @ _) (concat_1p _)).
Defined.

(** The cocone [col_A] induces [idmap : transfinite_A -> transfinite_A]. *)

Definition col_legs_induces_idmap `{Funext} {A : Sequence}
  {transfinite_A} (col_A : IsColimit A transfinite_A) 
  : cocone_postcompose_inv col_A col_A = idmap.
Proof.
  apply (@equiv_inj _ _ (cocone_postcompose col_A)
    (iscolimit_unicocone col_A transfinite_A) _ _).
  lhs snrapply (eisretr (cocone_postcompose col_A)).
  snrapply (cocone_postcompose_identity col_A)^.
Defined.

(** We show that the map induced by [succ_seq_to_seq] is an equivalence. *)

Section Is_Equiv_colim_succ_seq_to_seq_map.
  Context `{Funext} {A : Sequence}
    {transfinite_A : Type} (col_A : IsColimit A transfinite_A).

  (** The legs of [col_A] induces a cocone from [succ_seq A] 
    over [transfinite_A] *)

  Definition cocone_succ_seq_over_col 
    : Cocone (succ_seq A) transfinite_A
  := succ_seq_cocone_seq_cocone transfinite_A col_A.

  (** We start by showing that [abstr_colim_seq_to_abstr_colim_succ_seq]
      is a split-monomorphism. Observe that [cocone_succ_seq_over_col]
      essentially defines the same cocone as [col_A]. I.e. the following 
      diagram is commutative:
    
                  A          succ_seq A
               ______          ______
              |      | =====>  \     |
              |      |         /     |
               ‾‾‾‾‾‾          ‾‾‾‾‾‾
                   \  \     /  /
              col_A \  \   /  / cocone_succ_seq_over_col
                      colim A

  *)

  Definition legs_comm_cocone_succ_seq_over_col_with_col 
    (n : sequence_graph) 
    : cocone_precompose (seq_to_succ_seq A) cocone_succ_seq_over_col n
      == col_A n := (legs_comm (iscolimit_cocone col_A) _ _ _).

  Definition cocone_succ_seq_over_col_is_ess_col 
    : cocone_precompose (seq_to_succ_seq A) cocone_succ_seq_over_col
      = iscolimit_cocone col_A.
  Proof.
    apply (path_cocone 
      legs_comm_cocone_succ_seq_over_col_with_col).
    intros m n [] a. 
    unfold legs_comm_cocone_succ_seq_over_col_with_col.
    simpl.
    refine (ap (fun x => x @ legs_comm col_A m (S m) 1 a) (concat_1p _)).
  Defined.

  (* The cocone of [succ_seq A] over colim A is universal *)

  Instance iscolimit_succ_seq_A_over_transfinite_A : IsColimit (succ_seq A) transfinite_A.
  Proof.
  snrapply (Build_IsColimit cocone_succ_seq_over_col).
  snrapply Build_UniversalCocone.
  intro Y.
  srapply isequiv_adjointify.
  - intro C.
    exact (cocone_postcompose_inv col_A (cocone_precompose (seq_to_succ_seq A) C)).
  - intro C.
    snrapply (equiv_inj (cocone_precompose (seq_to_succ_seq A))).
    + exact (isequiv_cocone_precompose_seq_to_succ_seq (X:= Y)).
    + lhs_V snrapply cocone_precompose_postcompose.
      lhs snrapply (ap (fun x => cocone_postcompose x _)
        cocone_succ_seq_over_col_is_ess_col).
      snrapply (eisretr (cocone_postcompose col_A)).
  - intro f.
    snrapply (equiv_inj (cocone_postcompose col_A)).
    + exact (iscolimit_unicocone col_A Y).
    + lhs snrapply (eisretr (cocone_postcompose col_A)).
      lhs_V snrapply cocone_precompose_postcompose.
      snrapply (ap (fun x => cocone_postcompose x f) cocone_succ_seq_over_col_is_ess_col).
  Defined.

  (** Alias for the above instance. *)

  Definition col_succ := iscolimit_succ_seq_A_over_transfinite_A.

  (** We take the colimit of [seq_to_succ_seq]
      and obtain a map [transfinite_A -> transfinite_A] *)

  Definition abstr_colim_seq_to_abstr_colim_succ_seq
    : transfinite_A -> transfinite_A 
  := functor_colimit (seq_to_succ_seq A) col_A col_succ.

  Definition abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap
    : abstr_colim_seq_to_abstr_colim_succ_seq = idmap.
  Proof.
    unfold abstr_colim_seq_to_abstr_colim_succ_seq, functor_colimit.
    rewrite cocone_succ_seq_over_col_is_ess_col.
    snrapply (equiv_inj (cocone_postcompose col_A)).
    - snrapply (iscolimit_unicocone col_A).
    - lhs snrapply (eisretr (cocone_postcompose col_A)).
      snrapply (cocone_postcompose_identity col_A)^.
  Defined.

  (** The cocone [cocone_succ_seq_over_col] induces a map 
      [transfinite_A -> transfinite_A] *)

  Definition abstr_colim_succ_seq_to_abstr_colim_seq
    : transfinite_A -> transfinite_A 
  := (cocone_postcompose_inv col_succ cocone_succ_seq_over_col).

  Definition abstr_colim_succ_seq_to_abstr_colim_seq_is_idmap
    : abstr_colim_succ_seq_to_abstr_colim_seq = idmap.
  Proof.
    unfold abstr_colim_succ_seq_to_abstr_colim_seq.
    snrapply (equiv_inj (cocone_postcompose col_A)).
    - snrapply (iscolimit_unicocone col_A).
    - lhs snrapply (eisretr (cocone_postcompose col_A)).
      lhs snrapply (cocone_succ_seq_over_col_is_ess_col).
      snrapply (cocone_postcompose_identity col_A)^.
  Defined.

  (** The maps defined above are equivalences *)

  Definition sec_abstr_colim_seq_to_abstr_succ_seq
    : abstr_colim_succ_seq_to_abstr_colim_seq
    o abstr_colim_seq_to_abstr_colim_succ_seq
    = idmap.
  Proof.
    lhs snrapply (ap _ abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap).
    snrapply abstr_colim_succ_seq_to_abstr_colim_seq_is_idmap.
  Defined.

  Definition ret_abstr_colim_seq_to_abstr_succ_seq
    : abstr_colim_seq_to_abstr_colim_succ_seq 
    o abstr_colim_succ_seq_to_abstr_colim_seq
    = idmap.
  Proof.
    lhs snrapply (ap _ abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap).
    snrapply abstr_colim_succ_seq_to_abstr_colim_seq_is_idmap.
  Defined.

  (** [abstr_colim_seq_to_abstr_colim_succ_seq] is an equivalence *)
    
  Definition equiv_abstr_colim_seq_to_abstr_colim_succ_seq
    : IsEquiv abstr_colim_seq_to_abstr_colim_succ_seq.
  Proof.
    snrapply isequiv_adjointify.
    - exact abstr_colim_succ_seq_to_abstr_colim_seq.
    - exact (apD10 ret_abstr_colim_seq_to_abstr_succ_seq).
    - exact (apD10 sec_abstr_colim_seq_to_abstr_succ_seq).
  Defined.

End Is_Equiv_colim_succ_seq_to_seq_map.

(** Intersplitting is a pun of interleaving and splitting. 
    We will at first only assume that every other triangle
    is commutative. In this case, colim A is a retract of colim B. *)

Section Intersplitting.
  Context `{Funext} {A B : Sequence} 
    {transfinite_A : Type} (col_A : IsColimit A transfinite_A)
    {transfinite_B : Type} (col_B : IsColimit B transfinite_B)
    (d : DiagramMap A B) 
    (u : DiagramMap B (succ_seq A))
    (comm_triangle : seq_to_succ_seq A = diagram_comp u d).
    
  (** Given the data above, we show that the associated diagram in the
      colimit is also commutative.

                  ≃
        col A_i -----> col A_i+1
            \           ^
             \         /
              \       /
               v     /
              col B_i

      It follows that d is split-epi, and u is split-mono, as desired.
  *)

  Definition colimit_comm_triangle : 
    abstr_colim_seq_to_abstr_colim_succ_seq col_A
    = (functor_colimit u _ (col_succ col_A)) o (functor_colimit d _ _).
  Proof.
    rhs snrapply functor_colimit_compose.
    snrapply (ap (fun x => functor_colimit x col_A (col_succ col_A)) 
      comm_triangle).
  Defined.

  Definition colim_d_split_epi : 
    idmap = (functor_colimit u _ (col_succ col_A)) o (functor_colimit d _ _)
  := ((abstr_colim_seq_to_abstr_colim_succ_seq_is_idmap col_A)^ @ colimit_comm_triangle).

  Definition isequiv_colim_composite
    : IsEquiv ((functor_colimit u col_B (col_succ col_A)) 
      o (functor_colimit d col_A col_B)).
  Proof.
    apply (@isequiv_homotopic
      transfinite_A
      transfinite_A
      (abstr_colim_seq_to_abstr_colim_succ_seq col_A)
      ((functor_colimit u _ _) o (functor_colimit d _ _))
      (equiv_abstr_colim_seq_to_abstr_colim_succ_seq col_A)).
    apply apD10.
    exact colimit_comm_triangle.
  Defined.

End Intersplitting.

(** Now we will assume that every triangle is commutative.
    By the 2-out-of-6 property, it follows that every map in
    this diagram is an equivalence. *)

Section Interleaving.
  Context `{Funext} {A B : Sequence} 
    {transfinite_A : Type} (col_A : IsColimit A transfinite_A)
    {transfinite_B : Type} (col_B : IsColimit B transfinite_B)
    (d : DiagramMap A B) 
    (u : DiagramMap B (succ_seq A))
    (tri1 : seq_to_succ_seq A = diagram_comp u d)
    (tri2 : seq_to_succ_seq B = diagram_comp (succ_seq_map_seq_map d) u).

  Definition isequiv_interleaved_colim_maps
    : IsEquiv (functor_colimit d _ _) * IsEquiv (functor_colimit u _ (col_succ col_A)) * IsEquiv (functor_colimit (succ_seq_map_seq_map d) (col_succ col_A) (col_succ col_B)).
  Proof.
    snrapply two_out_of_six.
    - exact (isequiv_colim_composite col_A col_B d u tri1).
    - exact (isequiv_colim_composite col_B (col_succ col_A) u 
      (succ_seq_map_seq_map d) tri2).
  Defined.

  Definition equiv_interleaved_colim : transfinite_A <~> transfinite_B.
  Proof.
    snrapply Build_Equiv.
    - exact (functor_colimit d col_A col_B).
    - exact ((fst o fst) isequiv_interleaved_colim_maps).
  Defined.

End Interleaving.