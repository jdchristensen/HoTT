Require Import Basics Types.
Require Import Diagrams.Diagram.
Require Import Diagrams.Graph.
Require Import Diagrams.Cocone.
Require Import Diagrams.ConstantDiagram.
Require Import Colimits.Coeq.

Local Open Scope path_scope.
Generalizable All Variables.

(** This file contains the definition of colimits, and functoriality results on colimits. *)

(** * Colimits *)

(** A colimit is the extremity of a cocone. *)

Class IsColimit `(D: Diagram G) (Q: Type) := {
  iscolimit_cocone : Cocone D Q;
  iscolimit_unicocone : UniversalCocone iscolimit_cocone;
}.
(* Use :> and remove the two following lines,
   once Coq 8.16 is the minimum required version. *)
#[export] Existing Instance iscolimit_cocone.
Coercion iscolimit_cocone : IsColimit >-> Cocone.

Arguments Build_IsColimit {G D Q} C H : rename.
Arguments iscolimit_cocone {G D Q} C : rename.
Arguments iscolimit_unicocone {G D Q} H : rename.

(** [cocone_postcompose_inv] is defined for convenience: it is only the inverse of [cocone_postcompose]. It allows to recover the map [h] from a cocone [C']. *)

Definition cocone_postcompose_inv `{D: Diagram G} {Q X}
  (H : IsColimit D Q) (C' : Cocone D X) : Q -> X
  := @equiv_inv _ _ _ (iscolimit_unicocone H X) C'.

(** * Existence of colimits *)

(** Whatever the diagram considered, there exists a colimit of it. The existence is given by the HIT [colimit]. *)

(** ** Definition of the HIT 
<<
  HIT Colimit {G : Graph} (D : Diagram G) : Type :=
  | colim : forall i, D i -> Colimit D
  | colimp : forall i j (f : G i j) (x : D i) : colim j (D _f f x) = colim i x
  .
>>
*)

(** A colimit is just the coequalizer of the source and target maps of the diagram. *)
(** The source type in the coequalizer ought to be:
<<
{x : sig D & {y : sig D & {f : G x.1 y.1 & D _f f x.2 = y.2}}}
>>
However we notice that the path type forms a contractible component, so we can use the more efficient:
<<
{x : sig D & {j : G & G x.1 j}}
>>
*)
Definition Colimit {G : Graph} (D : Diagram G) : Type :=
  @Coeq
    {x : sig D & {j : G & G x.1 j}}
    (sig D)
    (fun t => t.1)
    (fun t => (t.2.1; D _f t.2.2 t.1.2))
  .

Definition colim {G : Graph} {D : Diagram G} (i : G) (x : D i) : Colimit D :=
  coeq (i ; x).

Definition colimp {G : Graph} {D : Diagram G} (i j : G) (f : G i j) (x : D i)
  : colim j (D _f f x) = colim i x
  := (cglue ((i; x); j; f))^.

Definition Colimit_ind {G : Graph} {D : Diagram G} (P : Colimit D -> Type)
(q : forall i x, P (colim i x))
(pp_q : forall (i j : G) (g: G i j) (x : D i),
  (@colimp G D i j g x) # (q j (D _f g x)) = q i x)
: forall w, P w.
Proof.
  srapply Coeq_ind.
  - intros [x i].
    exact (q x i).
  - intros [[i x] [j f]].
    cbn in f; cbn.
    apply moveR_transport_p.
    symmetry.
    exact (pp_q _ _ _ _).
Defined.

Definition Colimit_ind_beta_colimp {G : Graph} {D : Diagram G}
  (P : Colimit D -> Type) (q : forall i x, P (colim i x))
  (pp_q : forall (i j: G) (g: G i j) (x: D i),
    @colimp G D i j g x # q _ (D _f g x) = q _ x)
  (i j : G) (g : G i j) (x : D i)
  : apD (Colimit_ind P q pp_q) (colimp i j g x) = pp_q i j g x.
Proof.
  refine (apD_V _ _ @ _).
  apply moveR_equiv_M.
  apply moveR_equiv_M.
  refine (Coeq_ind_beta_cglue _ _ _ _ @ _).
  symmetry.
  apply moveL_transport_p_V.
Defined.

Definition Colimit_rec {G : Graph} {D : Diagram G} (P : Type) (C : Cocone D P)
  : Colimit D -> P.
Proof.
  srapply (Colimit_ind _ C).
  intros i j g x.
  refine (transport_const _ _ @ _).
  apply legs_comm.
Defined.

Definition Colimit_rec_beta_colimp {G : Graph} {D : Diagram G}
  (P : Type) (C : Cocone D P) (i j : G) (g: G i j) (x: D i)
  : ap (Colimit_rec P C) (colimp i j g x) = legs_comm C i j g x.
Proof.
  rapply (cancelL (transport_const (colimp i j g x) _)).
  srapply ((apD_const (Colimit_ind (fun _ => P) C _) (colimp i j g x))^ @ _).
  srapply (Colimit_ind_beta_colimp (fun _ => P) C _ i j g x).
Defined.

Arguments colim : simpl never.
Arguments colimp : simpl never.

(** Colimit_rec is an equivalence *)

Global Instance isequiv_colimit_rec `{Funext} {G : Graph}
  {D : Diagram G} (P : Type) : IsEquiv (Colimit_rec (D:=D) P).
Proof.
  srapply isequiv_adjointify.
  { intro f.
    srapply Build_Cocone.
    1: intros i g; apply f, (colim i g).
    intros i j g x.
    apply ap, colimp. }
  { intro.
    apply path_forall.
    srapply Colimit_ind.
    1: reflexivity.
    intros ????; cbn.
    nrapply transport_paths_FlFr'.
    apply equiv_p1_1q.
    apply Colimit_rec_beta_colimp. }
  { intros [].
    srapply path_cocone.
    1: reflexivity.
    intros ????; cbn.
    rewrite Colimit_rec_beta_colimp.
    hott_simpl. }
Defined.

Definition equiv_colimit_rec `{Funext} {G : Graph} {D : Diagram G} (P : Type)
  : Cocone D P <~> (Colimit D -> P) := Build_Equiv _ _ _ (isequiv_colimit_rec P).

(** And we can now show that the HIT is actually a colimit. *)

Definition cocone_colimit {G : Graph} (D : Diagram G) : Cocone D (Colimit D)
  := Build_Cocone colim colimp.

Global Instance unicocone_colimit `{Funext} {G : Graph} (D : Diagram G)
  : UniversalCocone (cocone_colimit D).
Proof.
  srapply Build_UniversalCocone; intro Y.
  srapply (isequiv_adjointify _ (Colimit_rec Y) _ _).
  - intros C.
    srapply path_cocone.
    1: reflexivity.
    intros i j f x; simpl.
    apply equiv_p1_1q.
    apply Colimit_rec_beta_colimp.
  - intro f.
    apply path_forall.
    srapply Colimit_ind.
    1: reflexivity.
    intros i j g x; simpl.
    nrapply (transport_paths_FlFr' (g:=f)).
    apply equiv_p1_1q.
    apply Colimit_rec_beta_colimp.
Defined.

Global Instance iscolimit_colimit `{Funext} {G : Graph} (D : Diagram G)
  : IsColimit D (Colimit D) := Build_IsColimit _ (unicocone_colimit D).

(** * Functoriality of colimits *)

Section FunctorialityColimit.

  Context `{Funext} {G : Graph}.

  (** Colimits are preserved by composition with a (diagram) equivalence. *)

  Definition iscolimit_precompose_equiv {D1 D2 : Diagram G}
    (m : D1 ~d~ D2) {Q : Type}
    : IsColimit D2 Q -> IsColimit D1 Q.
  Proof.
    intros HQ.
    srapply (Build_IsColimit (cocone_precompose m HQ) _).
    apply cocone_precompose_equiv_universality, HQ.
  Defined.

  Definition iscolimit_postcompose_equiv {D: Diagram G} `(f: Q <~> Q')
    : IsColimit D Q -> IsColimit D Q'.
  Proof.
    intros HQ.
    srapply (Build_IsColimit (cocone_postcompose HQ f) _).
    apply cocone_postcompose_equiv_universality, HQ.
  Defined.

  (** A diagram map [m] : [D1] => [D2] induces a map between any two colimits of [D1] and [D2]. *)

  Definition functor_colimit {D1 D2 : Diagram G} (m : DiagramMap D1 D2)
    {Q1 Q2} (HQ1 : IsColimit D1 Q1) (HQ2 : IsColimit D2 Q2)
    : Q1 -> Q2 := cocone_postcompose_inv HQ1 (cocone_precompose m HQ2).

  (** And this map commutes with diagram map. *)

  Definition functor_colimit_commute {D1 D2 : Diagram G}
    (m : DiagramMap D1 D2) {Q1 Q2}
    (HQ1 : IsColimit D1 Q1) (HQ2: IsColimit D2 Q2)
    : cocone_precompose m HQ2
      = cocone_postcompose HQ1 (functor_colimit m HQ1 HQ2)
    := (eisretr (cocone_postcompose HQ1) _)^.

  (** Additional coherence with postcompose and precompose *)

  Definition cocone_precompose_postcompose_comp {D1 D2 : Diagram G}
    (m : DiagramMap D1 D2) {Q1 Q2 : Type} (HQ1 : IsColimit D1 Q1)
    (HQ2 : IsColimit D2 Q2) {T : Type} (t : Q2 -> T)
    : cocone_postcompose HQ1 (t o (functor_colimit m HQ1 HQ2))
      = cocone_precompose m (cocone_postcompose HQ2 t).
    Proof.
      lhs nrapply cocone_postcompose_comp.
      lhs_V exact (ap (fun x => cocone_postcompose x t) 
        (functor_colimit_commute m HQ1 HQ2)).
      nrapply cocone_precompose_postcompose.
    Defined.

  (** Functoriality of colimits *)

  Definition postcompose_functor_colimit_compose {D1 D2 D3 : Diagram G} 
    (m : DiagramMap D1 D2) (n : DiagramMap D2 D3) 
    {Q1 Q2 Q3} (HQ1 : IsColimit D1 Q1) (HQ2 : IsColimit D2 Q2)
    (HQ3 : IsColimit D3 Q3)
    : cocone_postcompose HQ1 ((functor_colimit n HQ2 HQ3) o (functor_colimit m HQ1 HQ2))
      = cocone_postcompose HQ1 (functor_colimit (diagram_comp n m) HQ1 HQ3).
  Proof.
    lhs nrapply cocone_precompose_postcompose_comp.
    lhs_V nrapply (ap _ (functor_colimit_commute n HQ2 HQ3)).
    lhs nrapply cocone_precompose_comp.
    nrapply functor_colimit_commute.
  Defined.

  Definition functor_colimit_compose {D1 D2 D3 : Diagram G} 
    (m : DiagramMap D1 D2) (n : DiagramMap D2 D3) 
    {Q1 Q2 Q3} (HQ1 : IsColimit D1 Q1) (HQ2 : IsColimit D2 Q2)
    (HQ3 : IsColimit D3 Q3)
    : (functor_colimit n HQ2 HQ3) o (functor_colimit m HQ1 HQ2)
      = (functor_colimit (diagram_comp n m) HQ1 HQ3) 
    := @equiv_inj _ _ 
      (cocone_postcompose HQ1) (iscolimit_unicocone HQ1 Q3) _ _ 
      (postcompose_functor_colimit_compose m n HQ1 HQ2 HQ3).

  (** ** Colimits of equivalent diagrams *)

  (** Now we have than two equivalent diagrams have equivalent colimits. *)

  Context {D1 D2 : Diagram G} (m : D1 ~d~ D2) {Q1 Q2}
    (HQ1 : IsColimit D1 Q1) (HQ2 : IsColimit D2 Q2).

  Definition functor_colimit_eissect
    : functor_colimit m HQ1 HQ2
      o functor_colimit (diagram_equiv_inv m) HQ2 HQ1 == idmap.
  Proof.
    apply ap10.
    srapply (equiv_inj (cocone_postcompose HQ2) _).
    1: apply HQ2.
    etransitivity.
    2:symmetry; apply cocone_postcompose_identity.
    etransitivity.
    1: apply cocone_postcompose_comp.
    rewrite eisretr, cocone_precompose_postcompose, eisretr.
    rewrite cocone_precompose_comp, diagram_inv_is_section.
    apply cocone_precompose_identity.
  Defined.

  Definition functor_colimit_eisretr
    : functor_colimit (diagram_equiv_inv m) HQ2 HQ1
      o functor_colimit m HQ1 HQ2 == idmap.
  Proof.
    apply ap10.
    srapply (equiv_inj (cocone_postcompose HQ1) _).
    1: apply HQ1.
    etransitivity.
    2:symmetry; apply cocone_postcompose_identity.
    etransitivity.
    1: apply cocone_postcompose_comp.
    rewrite eisretr, cocone_precompose_postcompose, eisretr.
    rewrite cocone_precompose_comp, diagram_inv_is_retraction.
    apply cocone_precompose_identity.
  Defined.

  Global Instance isequiv_functor_colimit
    : IsEquiv (functor_colimit m HQ1 HQ2)
    := isequiv_adjointify _ _
      functor_colimit_eissect functor_colimit_eisretr.

  Definition equiv_functor_colimit : Q1 <~> Q2
    := Build_Equiv _ _ _ isequiv_functor_colimit.

End FunctorialityColimit.

(** * Unicity of colimits *)

(** A particuliar case of the functoriality result is that all colimits of a diagram are equivalent (and hence equal in presence of univalence). *)

Theorem colimit_unicity `{Funext} {G : Graph} {D : Diagram G} {Q1 Q2 : Type}
  (HQ1 : IsColimit D Q1) (HQ2 : IsColimit D Q2)
  : Q1 <~> Q2.
Proof.
  srapply equiv_functor_colimit.
  srapply (Build_diagram_equiv (diagram_idmap D)).
Defined.

(** * Colimits are left adjoint to constant diagram *)

Theorem colimit_adjoint `{Funext} {G : Graph} {D : Diagram G} {C : Type}
  : (Colimit D -> C) <~> DiagramMap D (diagram_const C).
Proof.
  symmetry.
  refine (equiv_colimit_rec C oE _).
  apply equiv_diagram_const_cocone.
Defined.

