Require Import Types.
Require Import Basics.
Require Import Colimits.GraphQuotient.
Require Import WildCat.

(** This file proves the induction principle for path spaces of coequalizers. This follows the paper PATH SPACES OF HIGHER INDUCTIVE TYPES
IN HOMOTOPY TYPE THEORY by Kraus and von Raumer. Their formalization can be found at https://gitlab.com/fplab/freealgstr. In the [FamilyCat] section we will define the categories C and D as described by this paper. C will be denoted as [ptd_family_with_relations], and D will be denoted as [ptd_family_graphquotient]. Since our final goal relies on the flatting lemma, we might want to assume univalence throughout the entire section. *)

Section FamilyCat.
  Context {A : Type} (a0 : A) (R : A -> A -> Type).

  (** [ptd_family_with_relations] is represents the wild category of pointed type families that respects relations. That is, if there is a term [r : R b c], then there is an equivalence [K b <~> K c]. *)

  Definition ptd_family_with_relations : Type 
    := {K : A -> Type & K a0 * forall b c : A, R b c -> K b <~> K c}.

  (** Accessor functions for [ptd_family_with_relations]. *)

  (** First projection *)
  Definition K_ : ptd_family_with_relations -> A -> Type := pr1.

  (** Second projection *)
  Definition r_ (Kre : ptd_family_with_relations) : K_ Kre a0 := fst (pr2 Kre).

  (** Third projection *)  
  Definition e_ (Kre : ptd_family_with_relations) {b c : A} 
    : R b c -> (K_ Kre) b <~> (K_ Kre) c := snd (pr2 Kre) b c.

  (** The arrows in this category is given by another triple. The first component is a collection of functions betwen the fibers of the type families. The second component is the assertion that this collection of functions respects the base point. The third component asserts that this collection is natural. *)

  Instance isgraph_ptd_family_with_relations : IsGraph ptd_family_with_relations.
  Proof.
    snrapply Build_IsGraph.
    intros Kre Kre'.
    exact {f : forall b : A, K_ Kre b -> K_ Kre' b 
      & (f a0 (r_ Kre) = r_ Kre') 
      * forall b c : A, forall s : R b c, 
        ((e_ Kre') s) o (f b) == (f c) o (e_ Kre) s}.
  Defined.

  (** Accessors functions for the homs of [ptd_family_with_relations]. *)

  (** first projection *)
  Definition f_ {Kre Kre' : ptd_family_with_relations} (f : Kre $-> Kre') (b : A)
    : K_ Kre b -> K_ Kre' b := pr1 f b.

  (** Second projection *)
  Definition d_ {Kre Kre' : ptd_family_with_relations} (f : Kre $-> Kre')
    : f_ f a0 (r_ Kre) = r_ Kre' := fst (pr2 f).

  (** Third projection *)
  Definition gamma_ {Kre Kre' : ptd_family_with_relations} (f : Kre $-> Kre') 
    {b c : A} (s : R b c) : (e_ Kre' s) o (f_ f b) == (f_ f c) o (e_ Kre s)
    := snd (pr2 f) b c s.

  (** [ptd_family_with_relations] defines a 1-category with morphism extensionality. *)

  Instance is01cat_ptd_family_with_relations : Is01Cat ptd_family_with_relations.
  Proof.
    snrapply Build_Is01Cat.
    - intro Kre.
      srefine (_ ; _).
      + intro a. exact idmap.
      + srefine (_ , _).
        * reflexivity.
        * intros b c s k. reflexivity.
    - intros Kre1 Kre2 Kre3 g f.
      srefine (_ ; _).
      + intro a. exact ((f_ g a) o (f_ f a)).
      + srefine (_ , _).
        * simpl. exact ((ap (f_ g a0) (d_ f)) @ d_ g).
        * intros b c s k.
          lhs nrapply (gamma_ g s).
          nrapply (ap (f_ g c) (gamma_ f s k)).
  Defined.

  (* I don't think these are the 2-cells that I want. At some point I need to use funext. *)
  Instance is2graph_ptd_family_with_relations : Is2Graph ptd_family_with_relations.
  Proof.
    intros Kre Kre'.
    snrapply Build_IsGraph.
    intros f g.
    exact {h : forall a x, f_ f a x = f_ g a x 
      & (h a0 (r_ Kre) @ d_ g = d_ f) 
      * (forall b c, forall s : R b c, forall x, (gamma_ f s x) @ (h c (e_ Kre s x)) 
        = (ap (e_ Kre' s) (h b x)) @ (gamma_ g s x))}.
  Defined.

  Instance is1cat_ptd_family_with_relations : Is1Cat ptd_family_with_relations.
  Proof.
    snrapply Build_Is1Cat'.
    - intros Kre Kre'.
      snrapply Build_Is01Cat.
      + intros f. snrefine (_ ; (_ , _)).
        * intros a x. reflexivity.
        * cbn. nrapply concat_1p.
        * intros b c s x. cbn.
          rhs nrapply concat_1p.
          nrapply concat_p1.
      + intros f g h p q. snrefine (_ ; (_ , _)).
        * intros a x. exact (pr1 q a x @ pr1 p a x).
        * cbn.
          lhs nrapply concat_pp_p.
          lhs nrapply (1 @@ fst (pr2 p)).
          nrapply (fst (pr2 q)).
        * intros b c s x. cbn.
          lhs nrapply concat_p_pp.
          lhs nrapply (snd (pr2 q) b c s x @@ 1).
          lhs nrapply concat_pp_p.
          lhs nrapply (1 @@ snd (pr2 p) b c s x).
          lhs nrapply concat_p_pp.
          nrapply whiskerR.
          nrapply (ap_pp _ _ _)^.
    - intros Kre Kre'.
      snrapply Build_Is0Gpd.
      + intros f g p. snrefine (_ ; (_ , _)).
        * intros a x. exact (pr1 p a x)^.
        * cbn. 
          nrapply moveR_Vp.
          exact (fst (pr2 p))^.
        * intros b c s x. cbn.
          nrapply moveR_pV.
          rhs nrapply concat_pp_p.
          rhs nrapply (ap_V _ _ @@ 1).
          nrapply moveL_Vp.
          nrapply (snd (pr2 p) _ _ _ _)^.
    - intros Kre Kre' Kre'' f.
      snrapply Build_Is0Functor.
      + intros g h p. snrefine (_ ; (_ , _)).
        * intros a x. cbn.
          apply (ap (f_ f a)).
          exact (pr1 p a x).
        * cbn.
          lhs nrapply concat_p_pp.
          nrapply whiskerR.
          lhs_V nrapply ap_pp.
          apply (ap (ap (f_ f a0))).
          exact (fst (pr2 p)).
        * intros b c s x. cbn.
          lhs nrapply concat_pp_p.
          lhs_V nrapply (1 @@ ap_pp _ _ _).
          lhs nrapply (1 @@ ap (ap (f_ f c)) (snd (pr2 p) b c s x)).
          lhs nrapply (1 @@ ap_pp _ _ _).
          lhs nrapply concat_p_pp.
          rhs nrapply concat_p_pp.
          nrapply whiskerR.
          rhs_V nrapply (ap_compose _ _ _ @@ 1).
          lhs_V nrapply (1 @@ ap_compose _ _ _).
          nrapply (concat_Ap (gamma_ _ _) _)^.
    - intros Kre Kre' Kre'' f.
      snrapply Build_Is0Functor.
      + intros g h p. snrefine (_ ; (_ , _)).
        * intros a x. cbn.
          exact (pr1 p a _).
        * cbn.
          lhs nrapply concat_p_pp.
          lhs_V nrapply (concat_Ap _ _ @@ 1).
          lhs nrapply concat_pp_p.
          nrapply whiskerL.
          exact (fst (pr2 p)).
        * intros b c s x. cbn.
          lhs nrapply concat_pp_p.
          lhs nrapply (1 @@ concat_Ap _ _).
          lhs nrapply concat_p_pp.
          rhs nrapply concat_p_pp.
          nrapply whiskerR.
          nrapply (snd (pr2 p)).
    - intros Kre Kre' Kre'' Kre''' f g h.
      snrefine (_ ; (_ , _)).
      + reflexivity.
      + unfold transport.
        lhs nrapply concat_1p.
        cbn.
        rhs nrapply concat_p_pp.
        nrapply whiskerR.
        lhs nrapply ap_pp.
        nrapply whiskerR.
        nrapply (ap_compose _ _ _)^.
      + intros b c s x. cbn.
        lhs nrapply concat_p1.
        rhs nrapply concat_1p.
        lhs nrapply concat_pp_p.
        nrapply whiskerL.
        lhs nrapply (1 @@ ap_compose _ _ _).
        nrapply (ap_pp _ _ _)^.
    - intros Kre Kre' f.
      snrefine (_ ; (_ , _)).
      + reflexivity.
      + unfold transport. cbn.
        lhs nrapply concat_1p.
        rhs nrapply concat_p1.
        nrapply (ap_idmap _)^.
      + intros b c s x. cbn.
        lhs nrapply concat_p1.
        apply (ap (fun x => 1 @ x)).
        nrapply ap_idmap.
    - intros Kre Kre' f.
      snrefine (_ ; (_ , _)).
      + reflexivity.
      + unfold transport. reflexivity.
      + intros b c s x. cbn.
        repeat lhs nrapply concat_p1.
        nrapply (concat_1p _)^.
  Defined.

  (** [ptd_family_graphquotient] represents the wild category of pointed type families over the graph quotient of R. *)

  Definition ptd_family_graphquotient : Type
    := {L : GraphQuotient R -> Type & L (gq a0)}.

  (** Accessor functions fpr [ptd_family_graphquotient]. *)

  (** First projection *)
  Definition L_ : ptd_family_graphquotient -> GraphQuotient R -> Type := pr1.

  (** Second projection *)
  Definition p_ (Lp : ptd_family_graphquotient) : L_ Lp (gq a0) := pr2 Lp.

  (** The arrows in this category is given by a touple. The first component is a collection of functions between the fibers of the type families. The second component is the assertion that this collection respects the basepoint. *)

  Instance isgraph_ptd_family_graphquotient : IsGraph ptd_family_graphquotient.
  Proof.
    snrapply Build_IsGraph.
    intros Lp Lp'.
    exact {g : forall x : GraphQuotient R, L_ Lp x -> L_ Lp' x 
      & g _ (p_ Lp) = p_ Lp'}.
  Defined.

  (** Accessor functions for the homs of [ptd_family_graphquotient]. *)

  (** First projection *)
  Definition g_ {Lp Lp' : ptd_family_graphquotient} (f : Lp $-> Lp') (x : GraphQuotient R) 
    : L_ Lp x -> L_ Lp' x := pr1 f x.

  (** Second projection *)
  Definition epsilon_ {Lp Lp' : ptd_family_graphquotient} (f : Lp $-> Lp') 
    : g_ f _ (p_ Lp) = p_ Lp' := pr2 f.

  (** [ptd_family_graphquotient] defines a 1-category with morphism extensionality. *)

  Instance is01cat_ptd_family_graphquotient : Is01Cat ptd_family_graphquotient.
  Proof.
    snrapply Build_Is01Cat.
    - intros Lp. srefine (_ ; _).
      + intro x. exact idmap.
      + reflexivity.
    - intros Lp Lp' Lp'' g f. srefine (_ ; _).
      + intro x. exact ((g_ g x) o (g_ f x)).
      + cbn.
        lhs nrapply (ap _ (epsilon_ f)).
        nrapply (epsilon_ g).
  Defined.

  (* I don't think these are the 2-cells that I want. At some point I need to use Funext. *)
  Instance is2graph_ptd_family_graphquotient : Is2Graph ptd_family_graphquotient.
  Proof.
    intros Lp Lp'.
    snrapply Build_IsGraph.
    intros f g. 
    exact {h : forall a, g_ f a == g_ g a & h (gq a0) (p_ Lp) @ epsilon_ g = epsilon_ f}.
  Defined.

  Instance is1cat_ptd_family_graphquotient : Is1Cat ptd_family_graphquotient.
  Proof.
    snrapply Build_Is1Cat'.
    - intros Lp Lp'.
      snrapply Build_Is01Cat.
      + intros f. snrefine (_ ; _).
        * intros a. reflexivity.
        * cbn. nrapply concat_1p.
      + intros f g h H2 H1. snrefine (_ ; _).
        * intros a x. exact (pr1 H1 a x @ pr1 H2 a x).
        * cbn.
          lhs snrapply concat_pp_p.
          lhs snrapply (1 @@ pr2 H2).
          snrapply (pr2 H1).
    - intros Lp Lp'.
      snrapply Build_Is0Gpd.
      intros f g H1. 
      snrefine (_ ; _).
      + intros a x. exact (pr1 H1 a x)^.
      + cbn. snrapply moveR_Vp.
        exact (pr2 H1)^.
    - intros Lp Lp' Lp'' f.
      snrapply Build_Is0Functor.
      intros g h H1.
      snrefine (_ ; _).
      + intros a x. cbn. 
        exact (ap (g_ f a) (pr1 H1 a x)).
      + cbn.
        lhs snrapply concat_p_pp.
        lhs_V snrapply (ap_pp _ _ _ @@ 1).
        snrapply (ap (fun x => ap _ x @ _) (pr2 H1)).
    - intros Lp Lp' Lp'' f.
      snrapply Build_Is0Functor.
      intros g h H1.
      snrefine (_ ; _).
      + intros a x. cbn.
        exact (pr1 H1 a _).
      + cbn.
        lhs nrapply concat_p_pp.
        lhs nrapply ((concat_Ap _ _)^ @@ 1).
        lhs nrapply concat_pp_p.
        snrefine (ap _ _ @ _).
        * exact (epsilon_ g).
        * nrapply (pr2 H1).
        * reflexivity.
    - intros Lp Lp' Lp'' Lp''' f g h.
      snrefine (_ ; _).
      + intros a x. reflexivity.
      + cbn.
        rhs nrapply concat_p_pp.
        lhs nrapply concat_1p.
        nrapply whiskerR.
        lhs nrapply ap_pp.
        nrapply whiskerR.
        nrapply (ap_compose _ _ _)^.
    - intros Lp Lp' f.
      snrefine (_ ; _).
      + intros a x. reflexivity.
      + cbn.
        lhs nrapply concat_1p.
        rhs nrapply concat_p1.
        nrapply (ap_idmap _)^.
    - intros Lp Lp' f.
      snrefine (_ ; _).
      * intros a x. reflexivity.
      * cbn.
        rhs nrapply concat_1p.
        nrapply concat_1p.
  Defined.

  (** The initial object of [ptd_family_graphquotient]. *)
  Definition initLp : ptd_family_graphquotient.
  Proof.
    srefine (_ ; _).
    - intro x. exact (gq a0 = x).
    - exact (idpath (gq a0)).
  Defined.

  Definition isinitial_initLp : IsInitial initLp.
  Proof.
    intro Lp.
    srefine (_ ; _).
    - srefine (_ ; _).
      + intros x []. exact (p_ Lp).
      + reflexivity.
    - intro f. cbn. 
      snrefine (_ ; _).
      + intros a []. 
        exact (epsilon_ f)^.
      + cbn. nrapply concat_Vp.
  Defined.

End FamilyCat.
