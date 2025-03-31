Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.Cocone.
Require Import Diagrams.Sequence.
Require Import Diagrams.CommutativeSquares.
Require Import Colimits.Colimit.
Require Import Colimits.Sequential.
Require Import Colimits.Pushout.

Local Open Scope nat_scope.

(* jdc: add the next few lines to Colimit.v, right after the definition.  Remove existing Arguments line. *)
Arguments colim {G D} & i x : simpl never.

(** A variant in which [D] is explicit, useful when [x] is not provided. *)
Definition colim' {G} D := @colim G D.
Arguments colim' {G} D & i x.
(** TODO: replace uses of [inj] in Sequential.v with [colim']. *)

(** * Colimits of interleaved sequences *)

(** Suppose we have sequences [A_i] and [B_i]. An interleaving from [A_i] to [B_i] consists of two natural transformations [f : A_i => B_i] and [g : B_i => A_i+1] such that the following diagram is commutative:

<<
    A_0 -------> A_1 ------> A_2 ------>
        \        ^  \        ^ 
         \      /    \      /  
          \    /      \    /         ...
           v  /        v  /
           B_0 ------> B_1 ------->
>>

Given the setup above, we want to say that the colimits of the upper and lower sequences are equivalent. *)

(** Given families of maps [f n : A n -> B n] and [g : B n -> A (n + 1)] with homotopies showing that they form zigzags, construct the actual diagram maps and show that their composition is equal to the successor diagram map. *)

(* jdc: In many cases, you should be able to assume that the homotopies are reflexivity, i.e. that the maps in the sequences are *definitionally* the composites of the diagonal maps.  (Under Funext, this is easy:  you just destruct the paths corresponding to the homotopies.)  To make this smoother in practice, I suspect that reversing the directions of [U] and [L] below might make it easier to destruct them within proofs. *)

Section Interme.
  Context {A B : Sequence}
    (f : forall (n : nat), A n -> B n)
    (g : forall (n : nat), B n -> A (S n))
    (U : forall (n : nat), (fun (x : A n) => x^+) == (g n) o (f n))
    (L : forall (n : nat), (fun (x : B n) => x^+) == (f (S n)) o (g n)).

  (** The map built from [f]. Note that [zigzag_glue_map_tri] depends heavily on the exact homotopy used here. *)
  Definition zigzag_glue_map : DiagramMap A B.
  Proof.
    snrapply Build_DiagramMap.
    - exact f.
    - intros n _ [] x.
      lhs apply (L n).
      exact (ap _ (U n x)^).
  Defined.

  (** The map built from [g]. *)
  Definition zigzag_glue_map_inv : DiagramMap B (succ_seq A).
  Proof.
    snrapply Build_DiagramMap.
    - exact g.
    - intros n _ [] x.
      lhs apply (U (S n)).
      exact (ap _ (L n x))^.
  Defined.

  Local Open Scope path_scope.

  (** Show that the composition of the two maps is the successor map. *)
  Definition zigzag_glue_map_tri : DiagramMap_homotopy (diagram_comp zigzag_glue_map_inv zigzag_glue_map) (seq_to_succ_seq A).
  Proof.
    snrapply (_; _).
    - intros n x.
      simpl.
      exact (U n x)^.
    - intros n _ [] x.
      simpl.
      Open Scope long_path_scope.
      rhs nrapply concat_p1.
      apply moveR_pV.
      lhs nrapply (1 @@ ap_pp _ _ _).
      lhs nrapply concat_pp_p.
      lhs nrapply (1 @@ concat_V_pp _ _).
      lhs_V nrapply (1 @@ ap_compose _ _ _).
      exact (concat_Ap _ _)^.
      Close Scope long_path_scope.
  Defined.
End Interme.

(** Assuming that there are [A, B : Sequence] that fit in an interleaving diagram, their colimits are isomorphic. *)

(** jdc: I'm not sure why we need a new section, since the Context is exactly the same: *)
Section Interleaving.
  Context {A B : Sequence} 
    (f : forall (n : nat), A n -> B n)
    (g : forall (n : nat), B n -> A (S n))
    (U : forall (n : nat), (fun (x : A n) => x^+) == (g n) o (f n))
    (L : forall (n : nat), (fun (x : B n) => x^+) == (f (S n)) o (g n)).

  Notation d := (zigzag_glue_map f g U L).

  Notation u := (zigzag_glue_map_inv f g U L).

  Definition zigzag_glue_map_inf : Colimit A -> Colimit B
    := functor_Colimit d.

  Definition zigzag_glue_map_inv_inf : Colimit B -> Colimit A
    := functor_Colimit_half u (Colimit_succ A).

  (** We will show that [zigzag_glue_map_inv_inf] is an equivalence with inverse [zigzag_glue_map_inf]. *)

  (** Below, we give a simple proof of [eisretr] using [zigzag_glue_map_tri] and functoriality of the colimit.  We could do the same for [eissect], but then we have trouble showing how it computes.  So we instead give the following proof. *)
  (* jdc: I rephrased the comment and renamed the result.  It's not a better section, but a better proof that a certain map *is* a section. *)
  (* jdc: I think it would be worth seeing again if the high-level proof could be made to work. *)
  Local Definition better_eissect : zigzag_glue_map_inf o zigzag_glue_map_inv_inf == idmap.
  Proof.
    snrapply Colimit_ind.
    - intros n x; simpl.
      rhs_V nrapply (glue B n).
      symmetry.
      apply ap, L.
    - intros n _ [] x.
      Open Scope long_path_scope.
      lhs nrapply transport_paths_FFlr.
      apply whiskerR.
      rewrite Colimit_rec_beta_colimp; simpl.
      rewrite ap_pp.
      rewrite Colimit_rec_beta_colimp; simpl.
      rewrite <- ap_compose; simpl.
      rewrite ! ap_V.
      rewrite ! ap_pp.
      rewrite ap_V.
      rewrite ! inv_pp.
      Opaque colimp.
      rewrite ! inv_V.
      rewrite ! concat_p_pp.
      rewrite 2 (ap_compose (f n.+2) _).
      rewrite ap_V.
      rewrite concat_pV_p.
      apply moveR_pM.
      rewrite concat_pp_p.
      rewrite <- ! ap_V.
      rewrite concat_pp_p.
      rewrite <- ap_pp.
      rewrite <- ap_pp.
      rewrite concat_p_pp.
      rewrite <- (ap_compose (g n.+1) (f n.+2)).
      rewrite <- (ap_homotopic (L n.+1)).
      apply moveL_pV.
      nrapply ap_colim'.
      Transparent colimp.
      Close Scope long_path_scope.
  Defined.

  (** The zigzag gluing map is an equivalence.  The original proof used [Interme] twice; first on the sequence, then shifting the sequence by one (using [B] and [succ_seq A] instead of [A] and [B], respectively). This required some bookkeeping to fix and the section produced by this method didn't have the necessary computation rule for the induction principle. *)
  Definition zigzag_glue_map_isequiv : IsEquiv zigzag_glue_map_inv_inf.
  Proof.
    snrapply isequiv_adjointify.
    - exact zigzag_glue_map_inf.
    - transitivity (functor_Colimit_half (diagram_comp u d) (Colimit_succ A)).
      + symmetry.
        exact (functor_Colimit_half_compose d u (Colimit_succ A)).
      + transitivity (functor_Colimit_half (seq_to_succ_seq A) (Colimit_succ A)).
        * exact (functor_Colimit_half_homotopy (zigzag_glue_map_tri f g U L) (Colimit_succ A)).
        * exact (Colimit_succ_map_is_idmap A).
    - exact better_eissect.
  Defined.

  Definition equiv_zigzag_glue : Colimit B <~> Colimit A.
  Proof.
    snrapply Build_Equiv.
    + exact zigzag_glue_map_inv_inf.
    + exact zigzag_glue_map_isequiv.
  Defined.

  (** Prove two computation rules needed for the induction principle: the section and retraction of the equivalence are the inverse of the two input homotopies [U] and [L] concatenated with [colimp] when applied to the colimit of sequence elements. *)

  (** That [concat_1p] proves this isn't obvious, but results from simplifying the expressions. *)
  Definition zigzag_comp_eisretr (n : nat) (a : A n)
    : eisretr equiv_zigzag_glue (colim n a)
      = ap (colim' A n.+1) (U n a)^ @ glue A n a
    := concat_1p _.

  Definition zigzag_comp_eissect (n : nat) (b : B n)
    : eissect equiv_zigzag_glue (colim n b)
      = ap (colim' B n.+1) (L n b)^ @ glue B n b.
  Proof.
    (* FIXME: This is trash. Some of this is induced by [isequiv_adjointify], is it easier to do that ourselves?  *)
    (* jdc: Extra junk does arise because of [isequiv_adjointify].  When restricted to the point constructors here, the extra junk is equal to reflexivity, but I'm not sure if that's true on the whole colimit, which is what you'd need to prove to show that your proofs of isretr and issect satisfy the adjointness condition. (And even if true, it's probably hard to prove.) *)
    Open Scope long_path_scope.
    simpl.
    rhs nrapply (ap_V _ _ @@ 1).
    rhs_V nrapply (concat_1p _).
    apply whiskerR.
    (* What remains on the LHS is the correction due to [isequiv_adjointify]. Surprisingly, that correction is reflexivity, and least when restricted to the point constructors. *)
    (* We strip the [ap zigzag_glue_map_inf] from everything. *)
    match goal with |- ap ?f ?p @ ap ?f ?q = _ => lhs_V exact (ap_pp f p q) end.
    nrapply (ap (y:=idpath) (ap zigzag_glue_map_inf)).
    (* Simplify a bit: *)
    unfold pointwise_paths_concat; simpl.
    rewrite concat_1p.
    (* Handle [ap zigzag_glue_map_inv_inf ...]. *)
    rewrite ap_V.
    rewrite ap_pp.
    rewrite 2 ap_V.
    rewrite <- (ap_compose _ zigzag_glue_map_inv_inf); simpl.
    rewrite Colimit_rec_beta_colimp; simpl.
    (* Now everything cancels pairwise. *)
    rewrite ap_V.
    rewrite 2 inv_pp.
    rewrite 2 inv_V.
    rewrite ap_pp. (* can use ap_pV after merging with latest Coq-HoTT *)
    rewrite ap_V.
    rewrite <- ap_compose.
    rewrite 2 concat_p_pp.
    rewrite concat_pV_p.
    rewrite concat_pp_V.
    apply concat_Vp.
    Close Scope long_path_scope.
  Defined.
End Interleaving.

Section InverseEquivCoh.

  (** Given type families [P : A -> Type], [Q : B -> Type], an equivalence [e : A <~> B], and a family of equivalences [f : forall (a : A), P a <~> Q (e a)], we get a family of equivalences [finv : forall (b : B), Q b <~> P (e^-1 b)] and some results about compositions of [f] and [finv]. *)

  Context {A B : Type} {P : A -> Type} {Q : B -> Type} (e : A <~> B) (f : forall (a : A), P a <~> Q (e a)).

  Definition finv : forall (b : B), Q b <~> P (e^-1 b).
  Proof.
    intro b.
    transitivity (Q (e (e^-1 b))).
    - snrapply equiv_transport.
      exact (eisretr e b)^.
    - symmetry.
      exact (f (e^-1 b)).
  Defined.

  Definition finv_f : forall (a : A), (finv (e a)) o (f a) == transport (fun y => P y) (eissect e a)^.
  Proof.
    intros a x.
    simpl.
    nrapply moveR_equiv_V'.
    lhs nrapply transport2.
    { lhs nrapply (ap _ (eisadj e a)).
      symmetry; apply ap_V. }
    (** jdc: the last step could be factored out as a lemma to do in PathGroupoids.v *)
    by destruct (eissect e a)^.
  Defined.

  Definition f_finv : forall (b : B), (f (e^-1 b)) o (finv b) == transport (fun y => Q y) (eisretr e b)^.
  Proof.
    intros b x.
    simpl.
    nrapply eisretr.
  Defined.
End InverseEquivCoh.
