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

(** We show that the map induced by [succ_seq_to_seq] is an equivalence. *)

Section Is_Equiv_colim_succ_seq_to_seq_map.
  Context `{Funext} {A : Sequence}
    {transfinite_A : Type} (col_A : IsColimit A transfinite_A)
    {transfinite_succ_A : Type} 
    (col_succ_A : IsColimit (succ_seq A) transfinite_succ_A).

  (** We take the colimit of [seq_to_succ_seq]
    and obtain a map [transfinite_A -> transfinite_succ_A] *)

  Definition abs_colim_seq_to_abs_colim_succ_seq
    : transfinite_A -> transfinite_succ_A 
  := functor_colimit (seq_to_succ_seq A) col_A col_succ_A.

  (** The legs of [col_A] induces a cocone from [succ_seq A] 
    over [transfinite_A] *)

  Definition cocone_succ_seq_over_col 
    : Cocone (succ_seq A) transfinite_A.
  Proof.
    srapply Build_Cocone.
    - intros n a. exact (col_A (S n) a).
    - intros m n [] a. exact (legs_comm col_A _ _ _ _).
  Defined.

  (** The cocone above induces a map [transfinite_succ_A -> transfinite_A] *)

  Definition abs_colim_succ_seq_to_abs_colim_seq
    : transfinite_succ_A -> transfinite_A 
  := (cocone_postcompose_inv col_succ_A cocone_succ_seq_over_col).

  (** Our goal is to show that these maps are quasi-inverses
      of each other. *)

  (** We start by showing that [abs_colim_seq_to_abs_colim_succ_seq]
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
    lhs refine 
      (ap (fun x => x @ legs_comm col_A m (S m) 1 a) (concat_1p _)).
    reflexivity.
  Defined.

  (** The cocone [col_A] induces [idmap : transfinite_A -> transfinite_A]. *)

  Definition col_legs_induces_idmap 
    : cocone_postcompose_inv col_A col_A = idmap.
  Proof.
    apply (@equiv_inj _ _ (cocone_postcompose col_A)
      (iscolimit_unicocone col_A transfinite_A) _ _).
    lhs snrapply (eisretr (cocone_postcompose col_A)).
    rhs snrapply (cocone_postcompose_identity col_A).
    reflexivity.
  Defined.

  (** [cocone_precompose (seq_to_succ_seq A) cocone_succ_seq_over_col] 
      induces the composite [abs_colim_succ_seq_to_abs_colim_seq
      o abs_colim_seq_to_abs_colim_succ_seq] *)

  Definition cocone_precompose_seq_to_succ_seq_cocone_succ_seq_over_col_induces_comp
    : cocone_postcompose_inv col_A (cocone_precompose (seq_to_succ_seq A) cocone_succ_seq_over_col)
    = abs_colim_succ_seq_to_abs_colim_seq
    o abs_colim_seq_to_abs_colim_succ_seq. 
  Proof.
    apply (@equiv_inj _ _ (cocone_postcompose col_A)
      (iscolimit_unicocone col_A transfinite_A) _ _).
    rhs snrapply cocone_postcompose_comp.
    unfold abs_colim_seq_to_abs_colim_succ_seq.
    rhs snrapply (ap (fun x => cocone_postcompose x 
      abs_colim_succ_seq_to_abs_colim_seq) 
      (functor_colimit_commute _ _ _)^).
    rhs snrapply cocone_precompose_postcompose.
    unfold abs_colim_succ_seq_to_abs_colim_seq.
    rhs snrapply (ap (fun x => cocone_precompose (seq_to_succ_seq A) x) 
      (eisretr (cocone_postcompose col_succ_A) cocone_succ_seq_over_col)).
    lhs snrapply (eisretr (cocone_postcompose col_A)).
    reflexivity.
  Defined.

  Definition sec_abs_colim_seq_to_abs_succ_seq
    : abs_colim_succ_seq_to_abs_colim_seq
    o abs_colim_seq_to_abs_colim_succ_seq
    = idmap.
  Proof.
    lhs snrapply cocone_precompose_seq_to_succ_seq_cocone_succ_seq_over_col_induces_comp^.
    lhs snrapply (ap (fun x => cocone_postcompose_inv col_A x) 
      cocone_succ_seq_over_col_is_ess_col).
    exact (col_legs_induces_idmap).
  Defined.

  (** Hack while I think about this property *)

    Definition ret_abs_colim_seq_to_abs_succ_seq
      : abs_colim_seq_to_abs_colim_succ_seq 
      o abs_colim_succ_seq_to_abs_colim_seq
      = idmap.
    Proof.
    Admitted.

  (** [abs_colim_seq_to_abs_colim_succ_seq] is an equivalence *)
    
  Definition equiv_abs_colim_seq_to_abs_colim_succ_seq
    : IsEquiv abs_colim_seq_to_abs_colim_succ_seq.
  Proof.
    snrapply isequiv_adjointify.
    - exact abs_colim_succ_seq_to_abs_colim_seq.
    - exact (apD10 ret_abs_colim_seq_to_abs_succ_seq).
    - exact (apD10 sec_abs_colim_seq_to_abs_succ_seq).
  Defined.

End Is_Equiv_colim_succ_seq_to_seq_map.

(** Intersplitting is a pun of interleaving and splitting. 
    We will at first only assume that every other triangle
    is commutative. In this case, colim A is a retract of colim B. *)

Section Intersplitting.
  Context `{Funext} {A B : Sequence} 
    {transfinite_A : Type} (col_A : IsColimit A transfinite_A)
    {transfinite_succ_A : Type} 
    (col_succ_A : IsColimit (succ_seq A) transfinite_succ_A)
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
    abs_colim_seq_to_abs_colim_succ_seq col_A col_succ_A 
    = (functor_colimit u _ _) o (functor_colimit d _ _).
  Proof.
    rhs snrapply functoriality_functor_colimit.
    rhs refine (ap (fun x => functor_colimit x col_A col_succ_A) 
      comm_triangle^).
    reflexivity.
  Defined.

  Definition isequiv_colim_composite
    : IsEquiv ((functor_colimit u col_B col_succ_A) o (functor_colimit d col_A col_B)).
  Proof.
    apply (@isequiv_homotopic
      transfinite_A
      transfinite_succ_A
      (abs_colim_seq_to_abs_colim_succ_seq col_A col_succ_A)
      ((functor_colimit u _ _) o (functor_colimit d _ _))
      (equiv_abs_colim_seq_to_abs_colim_succ_seq col_A col_succ_A)).
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
    {transfinite_succ_A : Type} (col_succ_A : IsColimit (succ_seq A) transfinite_succ_A)
    {transfinite_B : Type} (col_B : IsColimit B transfinite_B)
    {transfinite_succ_B : Type} (col_succ_B : IsColimit (succ_seq B) transfinite_succ_B)
    (d : DiagramMap A B) 
    (u : DiagramMap B (succ_seq A))
    (tri1 : seq_to_succ_seq A = diagram_comp u d)
    (tri2 : seq_to_succ_seq B = diagram_comp (succ_seq_map_seq_map d) u).

  Definition isequiv_interleaved_colim_maps
    : IsEquiv (functor_colimit d _ _) * IsEquiv (functor_colimit u _ _) * IsEquiv (functor_colimit (succ_seq_map_seq_map d) _ _).
  Proof.
    snrapply two_out_of_six.
    - exact (isequiv_colim_composite col_A col_succ_A col_B d u tri1).
    - exact (isequiv_colim_composite col_B col_succ_B col_succ_A u (succ_seq_map_seq_map d) tri2).
  Defined.

  Definition equiv_interleaved_colim : transfinite_A <~> transfinite_B.
  Proof.
    snrapply Build_Equiv.
    - exact (functor_colimit d col_A col_B).
    - exact ((fst o fst) isequiv_interleaved_colim_maps).
  Defined.

End Interleaving.