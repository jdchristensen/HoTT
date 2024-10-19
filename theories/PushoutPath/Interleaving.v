Require Import Basics.
Require Import Colimits.Pushout.
Require Import Spaces.Nat.
Require Import Basics.Tactics.
Require Import Diagrams.Cocone.
Require Import Diagrams.Diagram.
Require Import Diagrams.Sequence.
(* Require Import Diagrams.Graph. *)
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
    
    A_0 ----------> A_1 ------->
        \         ^    \        ^ 
         \       /      \      /  
          \     /        \    /         ...
           v   /          v  /
            B_0 --------> B_1 ------->
    
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

(** We need some lemmata involving coherences in transfinite compositions. *)

Section Transfinite_composition.
    Context `{Funext} {A : Sequence}
        (transfinite_A : Type) (col_A : IsColimit A transfinite_A)
        (transfinite_succ_A : Type) (col_succ_A : IsColimit (succ_seq A) transfinite_succ_A).

    (** This is a map colim [succ_seq A] to colim [A] *)

    Definition abs_colim_succ_seq_to_abs_colim_seq
        : transfinite_succ_A -> transfinite_A.
    Proof.
        apply (cocone_postcompose_inv col_succ_A).
        srapply Build_Cocone.
        - intros n a. exact (col_A (S n) a).
        - intros m n [] a. exact (legs_comm col_A _ _ _ _).
    Defined.

    (** This is a map colim [A] to colim [succ_seq A] *)

    Definition abs_colim_seq_to_abs_colim_succ_seq
        : transfinite_A -> transfinite_succ_A 
    := functor_colimit (seq_to_succ_seq A) _ _.

    (** We hope that these maps are quasi-inverses of each other *)
    
        (** Hack while I think about this property *)

        Definition ret_abs_colim_succ_seq_to_abs_seq
            : abs_colim_seq_to_abs_colim_succ_seq 
                o abs_colim_succ_seq_to_abs_colim_seq
                == idmap.
        Admitted.

        Definition sec_abs_colim_succ_seq_to_abs_seq
            : abs_colim_succ_seq_to_abs_colim_seq
                o abs_colim_seq_to_abs_colim_succ_seq
                == idmap.
        Admitted.

    Definition equiv_abs_colim_succ_seq_to_abs_colim_seq
        : IsEquiv abs_colim_succ_seq_to_abs_colim_seq.
    Proof.
        snrapply isequiv_adjointify.
        - exact abs_colim_seq_to_abs_colim_succ_seq.
        - exact sec_abs_colim_succ_seq_to_abs_seq.
        - exact ret_abs_colim_succ_seq_to_abs_seq.
    Defined.

End Transfinite_composition.

(** Intersplitting is a pun of interleaving and splitting. 
    We will at first only assume that every other triangle
    is commutative. Intuitively, one may think of A as a retract of B. 
    We then expect colim A to be a retract of colim B as well. *)

Section Intersplitting.
    Context `{Funext} {A B : Sequence} 
        (transfinite_A : Type) (col_A : IsColimit A transfinite_A)
        (transfinite_succ_A : Type) (col_succ_A : IsColimit (succ_seq A) transfinite_succ_A)
        (transfinite_B : Type) (col_B : IsColimit B transfinite_B)
        (d : DiagramMap A B) 
        (u : DiagramMap B (succ_seq A))
        (comm_triangle : seq_to_succ_seq A = diagram_comp u d).
    
    (** Given the data above, we show that the associated diagram in the
        colimit is also commutative.

        col A_i -----> col A_i+1
            \           ^
             \         /
              \       /
               v     /
              col B_i
    *)

    Definition colimit_comm_triangle : 
        (functor_colimit (seq_to_succ_seq A) col_A col_succ_A) 
          = (functor_colimit u _ _) o (functor_colimit d _ _).
    Proof.
        rhs snrapply functoriality_functor_colimit.
        rhs refine (ap (fun x => functor_colimit x col_A col_succ_A) 
            comm_triangle^).
        reflexivity.
    Defined.

End Intersplitting.

(** Now we will assume that every triangle is commutative. *)

Section Interleaving.
    Context {A B : Sequence} 
        (transfiniteA : Type) (colA : IsColimit A transfiniteA)
        (transfiniteB : Type) (colB : IsColimit B transfiniteB)
        (d : DiagramMap A B) 
        (u : DiagramMap B (succ_seq A))
        (tri1 : seq_to_succ_seq A = diagram_comp u d)
        (tri2 : seq_to_succ_seq B = diagram_comp (succ_seq_map_seq_map d) u).

End Interleaving.