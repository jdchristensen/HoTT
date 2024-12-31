Require Import Basics Types.
Require Import Diagrams.Diagram Diagrams.Graph Diagrams.Cocone
  Diagrams.ConstantDiagram Diagrams.CommutativeSquares.
Require Import Colimits.Coeq.
Require Import Homotopy.IdentitySystems.

Local Open Scope path_scope.
Generalizable All Variables.

(** This file contains the definition of colimits, and functoriality results on colimits. *)

(** * Colimits *)

(** ** Abstract definition *)

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

(** ** Existence of colimits *)

(** Every diagram has a colimit.  It could be described as the following HIT
<<
  HIT Colimit {G : Graph} (D : Diagram G) : Type :=
  | colim : forall i, D i -> Colimit D
  | colimp : forall i j (f : G i j) (x : D i) : colim j (D _f f x) = colim i x
  .
>>
but we instead describe it as the coequalizer of the source and target maps of the diagram.  The source type in the coequalizer ought to be:
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

(** The two ways of getting a path [colim j (D _f f x) = colim j (D _f f y)] from an path [x = y] are equivalent. *)
Definition ap_colim {G : Graph} {D : Diagram G} {i j : G} (f : G i j) {x y : D i} (p : x = y)
  : ap (colim j) (ap (D _f f) p)
    = colimp i j f x @ ap (colim i) p @ (colimp i j f y)^.
Proof.
  lhs_V nrapply ap_compose.
  exact (ap_homotopic (colimp i j f) p).
Defined.

(** The two ways of getting a path [colim i x = colim i y] from a path [x = y] are equivalent. *)
Definition ap_colim' {G : Graph} {D : Diagram G} {i j : G} (f : G i j) {x y : D i} (p : x = y)
  : ap (colim j) (ap (D _f f) p) @ colimp i j f y
    = colimp i j f x @ ap (colim i) p.
Proof.
  apply moveR_pM.
  apply ap_colim.
Defined.

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

(** The natural cocone to the colimit. *)
Definition cocone_colimit {G : Graph} (D : Diagram G) : Cocone D (Colimit D)
  := Build_Cocone colim colimp.

(** Given a cocone [C] and [f : Colimit D -> P] inducing a "homotopic" cocone, [Colimit_rec P C] is homotopic to [f]. *)
Definition Colimit_rec_homotopy {G : Graph} {D : Diagram G} (P : Type) (C : Cocone D P)
  (f : Colimit D -> P)
  (h_obj : forall i, legs C i == f o colim i)
  (h_comm : forall i j (g : G i j) x,
      legs_comm C i j g x @ h_obj i x = h_obj j ((D _f g) x) @ ap f (colimp i j g x))
  : Colimit_rec P C == f.
Proof.
  snrapply Colimit_ind.
  - simpl. exact h_obj.
  - cbn beta; intros i j g x.
    nrapply (transport_paths_FlFr' (colimp i j g x)).
    lhs nrapply (Colimit_rec_beta_colimp _ _ _ _ _ _ @@ 1).
    apply h_comm.
Defined.

(** "Homotopic" cocones induces homotopic maps. *)
Definition Colimit_rec_homotopy' {G : Graph} {D : Diagram G} (P : Type) (C1 C2 : Cocone D P)
  (h_obj : forall i, legs C1 i == legs C2 i)
  (h_comm : forall i j (g : G i j) x,
      legs_comm C1 i j g x @ h_obj i x = h_obj j ((D _f g) x) @ legs_comm C2 i j g x)
  : Colimit_rec P C1 == Colimit_rec P C2.
Proof.
  snrapply Colimit_rec_homotopy.
  - apply h_obj.
  - intros i j g x.
    rhs nrapply (1 @@ Colimit_rec_beta_colimp _ _ _ _ _ _).
    apply h_comm.
Defined.

(** [Colimit_rec] is an equivalence. *)
Global Instance isequiv_colimit_rec `{Funext} {G : Graph}
  {D : Diagram G} (P : Type)
  : IsEquiv (Colimit_rec (D:=D) P).
Proof.
  srapply isequiv_adjointify.
  - exact (cocone_postcompose (cocone_colimit D)).
  - intro f.
    apply path_forall.
    snrapply Colimit_rec_homotopy.
    1: reflexivity.
    intros; cbn.
    apply concat_p1_1p.
  - intros [].
    srapply path_cocone.
    1: reflexivity.
    intros; cbn.
    apply equiv_p1_1q.
    apply Colimit_rec_beta_colimp.
Defined.

Definition equiv_colimit_rec `{Funext} {G : Graph} {D : Diagram G} (P : Type)
  : Cocone D P <~> (Colimit D -> P) := Build_Equiv _ _ _ (isequiv_colimit_rec P).

(** It follows that the HIT Colimit is an abstract colimit. *)
Global Instance unicocone_colimit `{Funext} {G : Graph} (D : Diagram G)
  : UniversalCocone (cocone_colimit D).
Proof.
  srapply Build_UniversalCocone; intro Y.
  (* The goal is to show that [cocone_postcompose (cocone_colimit D)] is an equivalence, but that's the inverse to the equivalence we just defined. *)
  exact (isequiv_inverse (equiv_colimit_rec Y)).
Defined.

Global Instance iscolimit_colimit `{Funext} {G : Graph} (D : Diagram G)
  : IsColimit D (Colimit D)
  := Build_IsColimit _ (unicocone_colimit D).

(** ** Functoriality of concrete colimits *)

(** We will capitalize [Colimit] in the identifiers to indicate that these definitions relate to the concrete colimit defined above.  Below, we will also get functoriality for abstract colimits, without the capital C.  However, to apply those results to the concrete colimit uses [iscolimit_colimit], which requires [Funext], so it is also useful to give direct proofs of some facts. *)

(** We first work in a more general situation.  Any diagram map [m : D1 => D2] induces a map between the canonical colimit of [D1] and any cocone over [D2].  We use "half" to indicate this situation. *)
Definition functor_Colimit_half {G : Graph} {D1 D2 : Diagram G} (m : DiagramMap D1 D2) {Q} (HQ : Cocone D2 Q)
  : Colimit D1 -> Q.
Proof.
  apply Colimit_rec.
  refine (cocone_precompose m HQ).
Defined.

Definition functor_Colimit_half_beta_colimp {G : Graph} {D1 D2 : Diagram G} (m : DiagramMap D1 D2) {Q} (HQ : Cocone D2 Q) (i j : G) (g : G i j) (x : D1 i)
  : ap (functor_Colimit_half m HQ) (colimp i j g x) = legs_comm (cocone_precompose m HQ) i j g x
  := Colimit_rec_beta_colimp _ _ _ _ _ _.

(** Homotopic diagram maps induce homotopic maps. *)
Definition functor_Colimit_half_homotopy {G : Graph} {D1 D2 : Diagram G}
  {m1 m2 : DiagramMap D1 D2} (h : DiagramMap_homotopy m1 m2)
  {Q} (HQ : Cocone D2 Q)
  : functor_Colimit_half m1 HQ == functor_Colimit_half m2 HQ.
Proof.
  destruct h as [h_obj h_comm].
  snrapply Colimit_rec_homotopy'.
  - intros i x; cbn. apply ap, h_obj.
  - intros i j g x; simpl.
    Open Scope long_path_scope.
    (* TODO: Most of the work here comes from a mismatch between the direction of the path in [DiagramMap_comm] and [legs_comm] in the [Cocone] record, causing a reversal in [cocone_precompose].  There is no reversal in [cocone_postcompose], so I think [Cocone] should change. If that is done, then this result wouldn't be needed at all, and one could directly use [Colimit_rec_homotopy']. *)
    rewrite ap_V.
    lhs nrapply concat_pp_p.
    apply moveR_Vp.
    rewrite ! concat_p_pp.
    rewrite <- 2 ap_pp.
    rewrite h_comm.
    rewrite concat_pp_V.
    rewrite <- ap_compose.
    exact (concat_Ap (legs_comm HQ i j g) (h_obj i x))^.
    Close Scope long_path_scope.
Defined.

(** Now we specialize to the case where the second cone is a colimiting cone. *)
Definition functor_Colimit {G : Graph} {D1 D2 : Diagram G} (m : DiagramMap D1 D2)
  : Colimit D1 -> Colimit D2
  := functor_Colimit_half m (cocone_colimit D2).

(** A homotopy between diagram maps [m1, m2 : D1 => D2] gives a homotopy between the induced maps. *)
Definition functor_Colimit_homotopy {G : Graph} {D1 D2 : Diagram G}
  {m1 m2 : DiagramMap D1 D2} (h : DiagramMap_homotopy m1 m2)
  : functor_Colimit m1 == functor_Colimit m2
  := functor_Colimit_half_homotopy h _.

(** Composition of diagram maps commutes with [functor_Colimit_half], provided the first map uses [functor_Colimit]. *)
Definition functor_Colimit_half_compose {G : Graph} {A B C : Diagram G} (f : DiagramMap A B) (g : DiagramMap B C) {Q} (HQ : Cocone C Q)
  : functor_Colimit_half (diagram_comp g f) HQ == functor_Colimit_half g HQ o functor_Colimit f.
Proof.
  snrapply Colimit_rec_homotopy.
  - reflexivity.
  - intros i j k x; cbn.
    apply equiv_p1_1q.
    unfold comm_square_comp.
    Open Scope long_path_scope.
    lhs nrapply ((ap_V _ _) @@ 1).
    lhs nrapply ((inverse2 (ap_pp (HQ j) _ _)) @@ 1).
    lhs nrapply ((inv_pp _ _) @@ 1).
    symmetry.
    lhs nrapply (ap_compose (functor_Colimit f)).
    lhs nrapply (ap _ (Colimit_rec_beta_colimp _ _ _ _ _ _)).
    (* [legs_comm] unfolds to a composite of paths, but the next line works best without unfolding it. *)
    lhs nrapply ap_pp.
    lhs nrefine (1 @@ _). 1: nrapply functor_Colimit_half_beta_colimp.
    simpl.
    lhs nrapply concat_p_pp.
    nrefine (_ @@ 1).
    apply ap011.
    2: nrapply ap_V.
    lhs_V nrapply (ap_compose (colim j)); simpl.
    lhs nrapply (ap_V (HQ j o g j) _).
    apply ap, ap_compose.
    Close Scope long_path_scope.
Defined.

(** ** Functoriality of abstract colimits *)

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

  (** A diagram map [m : D1 => D2] induces a map between any two colimits of [D1] and [D2]. *)
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

  (** Additional coherence with postcompose and precompose. *)
  Definition cocone_precompose_postcompose_comp {D1 D2 : Diagram G}
    (m : DiagramMap D1 D2) {Q1 Q2 : Type} (HQ1 : IsColimit D1 Q1)
    (HQ2 : IsColimit D2 Q2) {T : Type} (t : Q2 -> T)
    : cocone_postcompose HQ1 (t o functor_colimit m HQ1 HQ2)
      = cocone_precompose m (cocone_postcompose HQ2 t).
    Proof.
      lhs nrapply cocone_postcompose_comp.
      lhs_V exact (ap (fun x => cocone_postcompose x t)
        (functor_colimit_commute m HQ1 HQ2)).
      nrapply cocone_precompose_postcompose.
    Defined.

  (** In order to show that colimits are functorial, we show that this is true after precomposing with the cocone. *)
  Definition postcompose_functor_colimit_compose {D1 D2 D3 : Diagram G}
    (m : DiagramMap D1 D2) (n : DiagramMap D2 D3)
    {Q1 Q2 Q3} (HQ1 : IsColimit D1 Q1) (HQ2 : IsColimit D2 Q2)
    (HQ3 : IsColimit D3 Q3)
    : cocone_postcompose HQ1 (functor_colimit n HQ2 HQ3 o functor_colimit m HQ1 HQ2)
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
    : functor_colimit n HQ2 HQ3 o functor_colimit m HQ1 HQ2
      = functor_colimit (diagram_comp n m) HQ1 HQ3
    := @equiv_inj _ _
      (cocone_postcompose HQ1) (iscolimit_unicocone HQ1 Q3) _ _
      (postcompose_functor_colimit_compose m n HQ1 HQ2 HQ3).

  (** ** Colimits of equivalent diagrams *)

  (** Now we have that two equivalent diagrams have equivalent colimits. *)

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

(** ** Unicity of colimits *)

(** A particuliar case of the functoriality result is that all colimits of a diagram are equivalent (and hence equal in presence of univalence). *)

Theorem colimit_unicity `{Funext} {G : Graph} {D : Diagram G} {Q1 Q2 : Type}
  (HQ1 : IsColimit D Q1) (HQ2 : IsColimit D Q2)
  : Q1 <~> Q2.
Proof.
  srapply equiv_functor_colimit.
  srapply (Build_diagram_equiv (diagram_idmap D)).
Defined.

(** ** Colimits are left adjoint to constant diagram *)

Theorem colimit_adjoint `{Funext} {G : Graph} {D : Diagram G} {C : Type}
  : (Colimit D -> C) <~> DiagramMap D (diagram_const C).
Proof.
  symmetry.
  refine (equiv_colimit_rec C oE _).
  apply equiv_diagram_const_cocone.
Defined.

(** ** Descent *)

Section Descent.

  Context `{Univalence}.

  (** Descent data over [f g : B -> A] is an "equifibrant" or "cartesian" type family [cd_fam : A -> Type].  This means that if [b : B], then the fibers [cd_fam (f b)] and [cd_fam (g b)] are equivalent, witnessed by [cd_e]. *)
  Record colDescent `{D : Diagram G} := {
    cold_fam {i : G} (di : D i) : Type;
    cold_e {i j : G} (g : G i j) (di : D i) : cold_fam (D _f g di) <~> cold_fam di
  }.

  Global Arguments colDescent {G} D.

  (** Let [A] and [B] be types, with a parallel pair [f g : B -> A]. *)
  Context `{D : Diagram G}.

  (** Descent data induces a type family over [Coeq f g]. *)
  Definition fam_coldescent (Pe : colDescent D)
    : Colimit D -> Type.
  Proof.
    snrapply (Colimit_rec _).
    - snrapply Build_Cocone.
      + intro i. exact (cold_fam Pe).
      + intros i j g di.
        rapply path_universe.
        exact (equiv_isequiv (cold_e Pe g di)).
  Defined.

  (** A type family over [Coeq f g] induces descent data. *)
  Definition coldescent_fam (P : Colimit D -> Type) : colDescent D.
  Proof.
    snrapply Build_colDescent.
    - intro i. exact (P o colim i).
    - intros i j g di.
      exact (equiv_transport P (colimp i j g di)).
  Defined.

  (** Transporting over [fam_cdescent] along [cglue b] is given by [cd_e]. *)
  Definition transport_fam_coldescent_colimp
    (Pe : colDescent D) {i j : G} (g : G i j) (di : D i) (pdg : cold_fam Pe (D _f g di))
    : transport (fam_coldescent Pe) (colimp i j g di) pdg = (cold_e Pe g di) pdg.
  Proof.
    nrapply transport_path_universe'.
    nrapply Colimit_rec_beta_colimp.
  Defined.

  (** A section on the descent data is a fiberwise section that respects the equivalences. *)
  Record colDescentSection {Pe : colDescent D} := {
    colds_sect {i : G} (di : D i) : cold_fam Pe di;
    colds_e {i j : G} (g : G i j) (di : D i) : cold_e Pe g di (colds_sect (D _f g di)) = colds_sect di
  }.

  Global Arguments colDescentSection Pe : clear implicits.

  (** A descent section induces a genuine section of [fam_cdescent Pe]. *)
  Definition coldescent_ind {Pe : colDescent D}
    (s : colDescentSection Pe)
    : forall (x : Colimit D), fam_coldescent Pe x.
  Proof.
    snrapply (Colimit_ind _).
    - intros i di. exact (colds_sect s di).
    - intros i j g di.
      exact (transport_fam_coldescent_colimp Pe g di _ @ colds_e s g di).
  Defined.

  (** We record its computation rule *)
  Definition coldescent_ind_beta_cglue {Pe : colDescent D}
    (s : colDescentSection Pe) {i j : G} (g : G i j) (di : D i)
    : apD (coldescent_ind s) (colimp i j g di) = transport_fam_coldescent_colimp Pe g di _ @ colds_e s g di
    := Colimit_ind_beta_colimp _ _ _ _ _ _ _.

  (** Dependent descent data over descent data [Pe : cDescent f g] consists of a type family [cdd_fam : forall a : A, cd_fam Pe a -> Type] together with coherences [cdd_e b pf]. *)
  Record colDepDescent {Pe : colDescent D} := {
    coldd_fam {i : G} (di : D i) (pdi : cold_fam Pe di) : Type;
    coldd_e {i j : G} (g : G i j) (di : D i) (pdg : cold_fam Pe (D _f g di))
      : coldd_fam (D _f g di) pdg <~> coldd_fam di (cold_e Pe g di pdg)
  }.

  Global Arguments colDepDescent Pe : clear implicits.

  (** A dependent type family over [fam_cdescent Pe] induces dependent descent data over [Pe]. *)
  Definition coldepdescent_fam {Pe : colDescent D}
    (Q : forall x : Colimit D, (fam_coldescent Pe) x -> Type)
    : colDepDescent Pe.
  Proof.
    snrapply Build_colDepDescent.
    - intros i di.
      exact (Q (colim i di)).
    - intros i j g di pdg; cbn.
      exact (equiv_transportDD (fam_coldescent Pe) Q
               (colimp i j g di) (transport_fam_coldescent_colimp Pe g di pdg)).
  Defined.

  (** Dependent descent data over [Pe] induces a dependent type family over [fam_cdescent Pe]. *)
  Definition fam_coldepdescent {Pe : colDescent D} (Qe : colDepDescent Pe)
    : forall (x : Colimit D), (fam_coldescent Pe x) -> Type.
  Proof.
    snrapply Colimit_ind.
    - intros i di. exact (coldd_fam Qe di).
    - intros i j g di; cbn.
      nrapply (moveR_transport_p _ (colimp i j g di)).
      funext pdg.
      rhs nrapply transport_arrow_toconst.
      rhs nrefine (ap (coldd_fam _ _) _).
      + exact (path_universe (coldd_e _ _ _ _)).
      + lhs nrapply (ap (fun x => (transport _ x _)) (inv_V (colimp _ _ _ _))).
        nrapply (transport_fam_coldescent_colimp _ _ _).
  Defined.

  (** A section of dependent descent data [Qe : cDepDescent Pe] is a fiberwise section [cdds_sect], together with coherences [cdds_e]. *)
  Record colDepDescentSection {Pe : colDescent D} {Qe : colDepDescent Pe} := {
    coldds_sect {i : G} (di : D i) (pdi : cold_fam Pe di) : coldd_fam Qe di pdi;
    coldds_e {i j : G} (g : G i j) (di : D i) (pdg : cold_fam Pe (D _f g di))
      : coldd_e Qe g di pdg (coldds_sect (D _f g di) pdg)
        = coldds_sect di (cold_e Pe g di pdg)
  }.

  Global Arguments colDepDescentSection {Pe} Qe.

  (** A dependent descent section induces a genuine section over the total space of [fam_cdescent Pe]. *)
  Definition coldepdescent_ind {Pe : colDescent D}
    {Q : forall (x : Colimit D), (fam_coldescent Pe) x -> Type}
    (s : colDepDescentSection (coldepdescent_fam Q))
    : forall (x : Colimit D) (px : fam_coldescent Pe x), Q x px.
  Proof.
    nrapply (Colimit_ind _).
    intros i j g di.
    apply dpath_forall.
    intro pdg.
    apply (equiv_inj (transport (Q (colim i di)) (transport_fam_coldescent_colimp Pe g di pdg))).
    rhs nrapply (apD (coldds_sect s di) (transport_fam_coldescent_colimp Pe g di pdg)).
    exact (coldds_e s g di pdg).
  Defined.

  (** The data for a section into a constant type family. *)
  Record colDepDescentConstSection {Pe : colDescent D} {Q : Type} := {
    colddcs_sect {i : G} (di : D i) (pdi : cold_fam Pe di) : Q;
    colddcs_e {i j : G} (g : G i j) (di : D i) (pdg : cold_fam Pe (D _f g di))
      : colddcs_sect (D _f g di) pdg = colddcs_sect di (cold_e Pe g di pdg)
  }.

  Global Arguments colDepDescentConstSection Pe Q : clear implicits.

  (** The data for a section of a constant family induces a section over the total space of [fam_cdescent Pe]. *)
  Definition coldepdescent_rec {Pe : colDescent D} {Q : Type}
    (s : colDepDescentConstSection Pe Q)
    : forall (x : Colimit D), fam_coldescent Pe x -> Q.
  Proof.
    nrapply (Colimit_ind _).
    intros i j g di.
    nrapply dpath_arrow.
    intro pdg.
    lhs nrapply transport_const.
    rhs nrapply (ap _ (transport_fam_coldescent_colimp Pe g di pdg)).
    exact (colddcs_e s g di pdg).
  Defined.

  (** Here is the computation rule on paths. *)
  Definition coldepdescent_rec_beta_colimp {Pe : colDescent D} {Q : Type}
    (s : colDepDescentConstSection Pe Q)
    {i j : G} (g : G i j) (di : D i) {pdi : cold_fam Pe di} {pdg : cold_fam Pe (D _f g di)} (pg : cold_e Pe g di pdg = pdi)
    : ap (sig_rec (coldepdescent_rec s)) (path_sigma _ (colim j (D _f g di); pdg) (colim i di; pdi) (colimp i j g di) (transport_fam_coldescent_colimp Pe g di pdg @ pg))
      = colddcs_e s g di pdg @ ap (colddcs_sect s _) pg.
  Proof.
    Open Scope long_path_scope.
    destruct pg.
    rhs nrapply concat_p1.
    lhs nrapply ap_sig_rec_path_sigma.
    lhs nrapply (ap (fun x => _ (ap10 x _) @ _)).
    { nrapply Colimit_ind_beta_colimp. }
    do 3 lhs nrapply concat_pp_p.
    apply moveR_Vp.
    lhs nrefine (1 @@ (1 @@ (_ @@ 1))).
    { nrapply (ap10_dpath_arrow (fam_coldescent Pe) (fun _ => Q) (colimp i j g di)). }
    lhs nrefine (1 @@ _).
    { lhs nrapply (1 @@ concat_pp_p _ _ _).
      lhs nrapply (1 @@ concat_pp_p _ _ _).
      lhs nrapply concat_V_pp.
      lhs nrapply (1 @@ concat_pp_p _ _ _).
      lhs nrapply (1 @@ (1 @@ (1 @@ (ap _ (concat_p1 _))))).
      nrapply (1 @@ (1 @@ concat_pV_p _ _)). }
    nrapply concat_V_pp.
    Close Scope long_path_scope.
  Defined. (** This is a lot slower than the other functions. <0.15s *)

  Definition coldepdescent_rec_beta_colimp' {Pe : colDescent D} {Q : Type}
  (s : colDepDescentConstSection Pe Q)
  {i j : G} (g : G i j) (di : D i) {pdg : cold_fam Pe (D _f g di)}
  : ap (sig_rec (coldepdescent_rec s)) (path_sigma _ (colim j (D _f g di); pdg) (colim i di; cold_e Pe g di pdg) (colimp i j g di) (transport_fam_coldescent_colimp Pe g di pdg))
    = colddcs_e s g di pdg.
  Proof.
    lhs_V nrapply (ap _ (ap _ (concat_p1 _))).
    rhs nrapply (concat_p1 _)^.
    nrapply coldepdescent_rec_beta_colimp.
  Defined.

End Descent. (** <0.15s *)

(** ** Flattening *)

Section Flattening.

  Context `{Univalence} `{D : Diagram G} (Pe : colDescent D).

  (** We mimic the constructors of [Coeq] for the total space.  Here is the point constructor, in curried form. *)
  Definition flatten_cold {i : G} {di : D i} (pdi : cold_fam Pe di) : sig (fam_coldescent Pe)
    := (colim i di; pdi).

  (** And here is the path constructor. *)
  Definition flatten_cold_colimp {i j : G} (g : G i j) (di : D i)
    {pdg : cold_fam Pe (D _f g di)} {pdi : cold_fam Pe di} (pg : cold_e Pe g di pdg = pdi)
    : flatten_cold pdg = flatten_cold pdi.
  Proof.
    snrapply path_sigma.
    - by apply colimp.
    - lhs nrapply transport_fam_coldescent_colimp.
      exact pg.
  Defined.

  (** Now that we've shown that [fam_coldescent Pe] acts like a [Colimit] of an appropriate diagram, we can use this to prove the flattening lemma.  The maps back and forth are very easy so this could almost be a formal consequence of the induction principle. *)
  Definition diagram_coldescent : Diagram G.
  Proof.
    snrapply Build_Diagram.
    - exact (fun x => { dx : D x & cold_fam Pe dx}).
    - intros i j g [di pdi].
      exact (D _f g di; (cold_e Pe g di)^-1 pdi).
  Defined.

  Lemma equiv_cold_flatten : sig (fam_coldescent Pe) <~>
    Colimit diagram_coldescent.
  Proof.
    snrapply equiv_adjointify.
    - nrapply sig_rec.
      nrapply coldepdescent_rec.
      snrapply Build_colDepDescentConstSection.
      + intros i di pdi.
        exact (@colim _ diagram_coldescent i (di; pdi)).
      + intros i j g di pdg; cbn.
        lhs nrapply (ap (colim j)).
        * nrapply (ap (fun x => (_; x))).
          symmetry.
          rapply (eissect (cold_e _ _ _)).
        * snrapply (@colimp _ diagram_coldescent i j g (di; cold_e Pe g di pdg)).
    - snrapply Colimit_rec.
      + snrapply Build_Cocone.
        * intros i [di pdi].
          exact (colim i di; pdi).
        * intros i j g [di pdi].
          snrapply path_sigma'.
          { nrapply colimp. }
          { lhs nrapply transport_fam_coldescent_colimp.
            nrapply eisretr. }
    - snrapply Colimit_ind.
      { reflexivity. }
      intros i j g [di pdi].
      nrapply transport_paths_FFlr'; nrapply equiv_p1_1q.
      lhs nrapply ap.
      {nrapply Colimit_rec_beta_colimp. }
      lhs nrapply coldepdescent_rec_beta_colimp.
      lhs_V nrapply (((ap_compose _ (colim _) _) @@ 1) @@ 1).
      lhs nrapply concat_pp_p.
      lhs nrapply (ap_V _ (eissect (cold_e Pe g di) _) @@ 1).
      nrapply moveR_Vp.
      lhs_V nrapply (1 @@ (ap_path_sigma_1p (fun d pd => @colim _ diagram_coldescent _ (d; pd)) _ _)).
      lhs_V nrapply (concat_Ap (@colimp _ diagram_coldescent i j g) (path_sigma' _ _ _)).
      f_ap.
      lhs nrapply (ap_path_sigma_1p (fun dx x => colim j (diagram_coldescent _f g (dx; x)))).
      rhs rapply (ap _ (eisadj (cold_e Pe g di)^-1 pdi)).
      exact (ap_compose _ (fun x => @colim _ diagram_coldescent j (D _f g di; x)) _).
    - intros [x px]; revert x px.
      nrapply coldepdescent_ind.
      snrapply (Build_colDepDescentSection).
      { reflexivity. }
      intros i j g di pdg; cbn.
      lhs nrapply transportDD_is_transport.
      nrapply transport_paths_FFlr'; nrapply equiv_p1_1q.
      lhs nrapply (ap _ (coldepdescent_rec_beta_colimp' _ _ _)).
      lhs_V nrapply (ap _ ((ap_compose _ _ _) @@ 1)).
      lhs nrapply (ap_pp _ _ (@colimp _ diagram_coldescent i j g (di; cold_e Pe g di pdg))).
      lhs nrapply (1 @@ (@Colimit_rec_beta_colimp _ diagram_coldescent _ _ _ _ _ (di; cold_e Pe g di pdg))).
      lhs_V nrapply ((ap_compose (fun x => @colim _ diagram_coldescent _ (_ ; x)) (Colimit_rec _ _) _) @@ 1).
      simpl.
      lhs nrefine (1 @@ _).
      { nrapply (ap (path_sigma' _ _)).
        exact (1 @@ (eisadj _ _)). }
      lhs nrapply (1 @@ path_sigma_p1_pp' _ _ _ _).
      lhs nrefine (1 @@ (1 @@ _)).
      { lhs_V nrapply (ap_exist _ _ _ _ _).
        exact (ap_compose _ _ _)^. }
      lhs nrapply (ap_V _ _ @@ 1).
      nrapply moveR_Vp.
      exact (concat_Ap (fun x => path_sigma' _ _
        (transport_fam_coldescent_colimp _ _ _ x)) _)^.
  Defined. (** This is slow. <0.2s *)

End Flattening. (** <0.15s *)

(** ** Characterization of path spaces *)

(** A pointed type family over an arbitrary colimit has an identity system structure precisely when its associated descent data satisfies Kraus and von Raumer's induction principle, https://arxiv.org/pdf/1901.06022. *)

Section Paths.

  (** Let [D : Diagram G] be a diagram with shape [G : Graph], together with a distinguished point [di0 : D i0] over [i0 : G].  Let [Pe : colDescent D] be descent data over the diagram [D] with the distinguished point [pdi0 : cold_fam Pe i0].  Assume that any dependent descent data [Qe : colDepDescent Pe] with a distinguished point [qi0 : coldd_fam Qe i0 pdi0] has a section that respects the distinguished points.  This is the induction principle provided by Kraus and von Raumer. *)
  Context `{Univalence} `{D : Diagram G} (Pe : colDescent D)
    (i0 : G) (di0 : D i0) (pdi0 : cold_fam Pe di0)
    (based_coldepdescent_ind : forall (Qe : colDepDescent Pe) (qi0 : coldd_fam Qe di0 pdi0),
      colDepDescentSection Qe)
    (based_coldepdescent_ind_beta : forall (Qe : colDepDescent Pe) (qi0 : coldd_fam Qe di0 pdi0),
      coldds_sect (based_coldepdescent_ind Qe qi0) di0 pdi0 = qi0).

  (** Under these hypotheses, we get an identity system structure on [fam_coldescent Pe]. *)
  Local Instance idsys_flatten_coldescent
    : @IsIdentitySystem _ (colim i0 di0) (fam_coldescent Pe) pdi0.
  Proof.
    snrapply Build_IsIdentitySystem.
    - intros Q q0 x p.
      snrapply coldepdescent_ind.
      by apply based_coldepdescent_ind.
    - intros Q q0; cbn.
      nrapply (based_coldepdescent_ind_beta (coldepdescent_fam Q)).
  Defined.

  (** It follows that the fibers [fam_coldescent Pe x] are equivalent to path spaces [(colim i0 di0) = x]. *)
  Definition induced_fam_cold_equiv_path (x : Colimit D)
    : (colim i0 di0) = x <~> fam_coldescent Pe x
    := @equiv_transport_identitysystem _ (colim i0 di0) (fam_coldescent Pe) pdi0 _ x.

End Paths.
