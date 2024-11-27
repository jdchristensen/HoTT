Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Forall.
Require Import Homotopy.IdentitySystems.
Require Import Colimits.GraphQuotient.

(** * Characterization of identity types of graph quotients *)

(** A pointed type family over a graph quotient has an identity system structure precisely when its associated descent data satisfies Kraus and von Raumer's induction principle, https://arxiv.org/pdf/1901.06022. *)
Section DescentGQ.

  (** Consider a graph [A] with arrows [R]. *)
  Context `{Univalence} {A : Type} (R : A -> A -> Type).

  (** Descent data over [A] and [R] is a type family [P_A : A -> Type], such that if [a b : A] is related by [r : R a b], then the fibers [P_A a] and [P_A b] are equivalent, witnessed by [e_P]. *)
  Context (P_A : A -> Type) (e_P : forall a b : A, R a b -> P_A a <~> P_A b).

  (** The first two arguments of [e_P] are taken to be implicit. *)
  Arguments e_P {_ _} _.

  (** The descent data bundles up to a type family of [GraphQuotient R]. *)
  Definition gq_bundle_descent : GraphQuotient R -> Type.
  Proof.
    snrapply (GraphQuotient_rec P_A).
    intros a b r.
    exact (path_universe_uncurried (e_P r)).
  Defined.

  (** [transport] of [gqglue r] over [gq_bundle_descent] is given by [e_P]. *)
  Definition transport_gqglue_bundle {a b : A} (r : R a b) (pa : P_A a) : transport gq_bundle_descent (gqglue r) pa = e_P r pa.
  Proof.
    nrapply transport_path_universe'.
    nrapply GraphQuotient_rec_beta_gqglue.
  Defined.

  Section DependentDescentWithFamily.

    (** Consider a dependent type family over [GraphQuotient R] and [gq_bundle_descent]. *)
    Context (Q : forall x : GraphQuotient R, gq_bundle_descent x -> Type).

    (** The dependent descent data is given by the following maps. *)
    Definition gq_descentfam_A (a : A) (pa : P_A a) : Type := Q (gq a) pa.

    Definition gq_descentfam_e {a b : A} (r : R a b) {pa : P_A a} : gq_descentfam_A a pa <~> gq_descentfam_A b (e_P r pa)
    := equiv_transportDD gq_bundle_descent Q (gqglue r) (transport_gqglue_bundle r pa).

    (** A section of the dependent descent data is given by a section [f_A], together with coherences [e_f]. *)
    Context (f_A : forall a : A, forall pa : P_A a, gq_descentfam_A a pa)
      (e_f : forall a b : A, forall r :  R a b, forall pa : P_A a, gq_descentfam_e r (f_A a pa) = f_A b (e_P r pa)).

    (** The first two arguments of [e_f] are taken to be implicit. *)
    Arguments e_f {_ _} _ _.

    (** Transporting over [Q] along [gqglue] is evaluation at the other endpoint on an edge. *)
    Definition gqglue_descentfam_sect (a b : A) (r : R a b)
      : transport (fun x : GraphQuotient R => forall px : gq_bundle_descent x, Q x px)
        (gqglue r) (f_A a) = f_A b.
    Proof.
      apply dpath_forall.
      intro pa.
      apply (equiv_inj (transport (gq_descentfam_A b) (transport_gqglue_bundle r pa))).
      rhs nrapply (apD (f_A b) (transport_gqglue_bundle r pa)).
      exact (e_f r pa).
    Defined.

    (** The section of dependent descent data bundles to a genuine section on the total space. *)
    Definition gq_descentfam_sect : forall x : GraphQuotient R, forall px : gq_bundle_descent x, Q x px
      := GraphQuotient_ind _ f_A gqglue_descentfam_sect.

    Definition gq_descentfam_sect_beta_gqglue (a b : A) (r : R a b)
      : apD gq_descentfam_sect (gqglue r) = gqglue_descentfam_sect a b r
      := GraphQuotient_ind_beta_gqglue _ f_A gqglue_descentfam_sect a b r.

  End DependentDescentWithFamily.

  Section DescentIdSys.

    (** Assume [A] and [P_A] are pointed types. *)
    Context {a0 : A} {p0 : P_A a0}.

    (** Assume for any pointed dependent descent data [Q_A], [e_Q], and [q0] that there are sections from the pointed descent data [P_A], [e_P], and [p0]. This is the Kraus-von Raumer induction principle. *)
    Context (gq_desc_idsys_ind : forall Q_A : forall a : A, P_A a -> Type,
        forall e_Q : forall a b : A, forall r : R a b, forall pa : P_A a, Q_A a pa <~> Q_A b (e_P r pa),
        forall q0 : Q_A a0 p0,
        forall a : A, forall pa : P_A a, Q_A a pa)
      (gqglue_desc_idsys_ind : forall Q_A : forall a : A, P_A a -> Type,
        forall e_Q : forall a b : A, forall r : R a b, forall pa : P_A a, Q_A a pa <~> Q_A b (e_P r pa),
        forall q0 : Q_A a0 p0, forall a b : A, forall r :  R a b, forall pa : P_A a,
        e_Q a b r pa (gq_desc_idsys_ind Q_A e_Q q0 a pa) = gq_desc_idsys_ind Q_A e_Q q0 b (e_P r pa))
      (gq_desc_idsys_ind_beta : forall Q_A : forall a : A, P_A a -> Type,
        forall e_Q : forall a b : A, forall r : R a b, forall pa : P_A a, Q_A a pa <~> Q_A b (e_P r pa),
        forall q0 : Q_A a0 p0,
        gq_desc_idsys_ind Q_A e_Q q0 a0 p0 = q0).

    (** Kraus-von Raumer induction induces an identity system structure on [gq_bundle_descent]. *)
    Local Instance identitysystem_gq_bundle_descent : @IsIdentitySystem _ (gq a0) gq_bundle_descent p0.
    Proof.
      snrapply Build_IsIdentitySystem.
      - intros Q q0 x p.
        snrapply gq_descentfam_sect.
        + exact (gq_desc_idsys_ind (gq_descentfam_A Q) (@gq_descentfam_e Q) q0).
        + apply gqglue_desc_idsys_ind.
      - intros Q q0; cbn.
        nrapply gq_desc_idsys_ind_beta.
    Defined.

    Definition gq_bundle_descent_equiv_path (x : GraphQuotient R)
      : (gq a0) = x <~> gq_bundle_descent x
      := @equiv_transport_identitysystem (GraphQuotient R) (gq a0) gq_bundle_descent p0 _ x.

  End DescentIdSys.
End DescentGQ.
