Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Forall.
Require Import Homotopy.IdentitySystems.
Require Import Colimits.Coeq.

(** * Characterization of identity types of coequalizers *)

(** A pointed type family over a coequalizer has an identity system structure precisely when its associated descent data satisfies Kraus and von Raumer's induction principle, https://arxiv.org/pdf/1901.06022.  *)
Section DescentCoeq.

  (** Consider a double arrow. *)
  Context `{Univalence} {A B : Type} (f g : B -> A).

  (** Descent data over [f] and [g] is a type family [P_A : A -> Type], such that for any [b : B], the fibers [P_A (f a)] and [P_A (g a)] are equivalent, witnessed by [e_P]. *)
  Context (P_A : A -> Type) (e_P : forall b : B, P_A (f b) <~> P_A (g b)).

  (** The descent data bundles up to a type family of [GraphQuotient R]. *)
  Definition c_bundle_descent : Coeq f g -> Type.
  Proof.
    snrapply (Coeq_rec _ P_A).
    intro b.
    exact (path_universe_uncurried (e_P b)).
  Defined.

  (** [transport] of [cglue r] over [c_bundle_descent] is given by [e_P]. *)
  Definition transport_cglue_bundle (b : B) (pa : P_A (f b)) : transport c_bundle_descent (cglue b) pa = e_P b pa.
  Proof.
    nrapply transport_path_universe'.
    nrapply Coeq_rec_beta_cglue.
  Defined.

  Section DependentDescentWithFamily.

    (** Consider a dependent type family over [Coeq f g] and [c_bundle_descent]. *)
    Context (Q : forall x : Coeq f g, c_bundle_descent x -> Type).

    (** The dependent descent data is given by the following maps. *)
    Definition c_descentfam_A (a : A) (pa : P_A a) : Type := Q (coeq a) pa.

    Definition c_descentfam_e (b : B) {pa : P_A (f b)} : c_descentfam_A (f b) pa <~> c_descentfam_A (g b) (e_P b pa)
    := equiv_transportDD c_bundle_descent Q (cglue b) (transport_cglue_bundle b pa).

    (** A section of the dependent descent data is given by a section [f_A], together with coherences [e_f]. *)
    Context (f_A : forall a : A, forall pa : P_A a, c_descentfam_A a pa)
      (e_f : forall b : B, forall pa : P_A (f b), c_descentfam_e b (f_A (f b) pa) = f_A (g b) (e_P b pa)).

    (** Transporting over [Q] along [cglue] is evaluation at the other endpoint on an edge. *)
    Definition cglue_descentfam_sect (b : B)
      : transport (fun x : Coeq f g => forall px : c_bundle_descent x, Q x px)
        (cglue b) (f_A (f b)) = f_A (g b).
    Proof.
      apply dpath_forall.
      intro pa.
      apply (equiv_inj (transport (c_descentfam_A (g b)) (transport_cglue_bundle b pa))).
      rhs nrapply (apD (f_A (g b)) (transport_cglue_bundle b pa)).
      exact (e_f b pa).
    Defined.

    (** The section of dependent descent data bundles to a genuine section on the total space. *)
    Definition c_descentfam_sect
      : forall x : Coeq f g, forall px : c_bundle_descent x, Q x px
      := Coeq_ind _ f_A cglue_descentfam_sect.

    Definition c_descentfam_sect_beta_cglue (b : B)
      : apD c_descentfam_sect (cglue b) = cglue_descentfam_sect b
      := Coeq_ind_beta_cglue _ f_A cglue_descentfam_sect b.

  End DependentDescentWithFamily.

  Section DescentIdSys.

    (** Assume [A] and [P_A] are pointed types. *)
    Context {a0 : A} {p0 : P_A a0}.

    (** Assume for any pointed dependent descent data [Q_A], [e_Q], and [q0] that there are sections from the pointed descent data [P_A], [e_P], and [p0]. This is the Kraus-von Raumer induction principle. *)
    Context (c_desc_idsys_ind : forall Q_A : forall a : A, P_A a -> Type,
        forall e_Q : forall b : B, forall pa : P_A (f b), Q_A (f b) pa <~> Q_A (g b) (e_P b pa),
        forall q0 : Q_A a0 p0,
        forall a : A, forall pa : P_A a, Q_A a pa)
      (c_glue_desc_idsys_ind : forall Q_A : forall a : A, P_A a -> Type,
        forall e_Q : forall b : B, forall pa : P_A (f b), Q_A (f b) pa <~> Q_A (g b) (e_P b pa),
        forall q0 : Q_A a0 p0, forall b : B, forall pa : P_A (f b),
        e_Q b pa (c_desc_idsys_ind Q_A e_Q q0 (f b) pa) = c_desc_idsys_ind Q_A e_Q q0 (g b) (e_P b pa))
      (c_desc_idsys_ind_beta : forall Q_A : forall a : A, P_A a -> Type,
        forall e_Q : forall b : B, forall pa : P_A (f b), Q_A (f b) pa <~> Q_A (g b) (e_P b pa),
        forall q0 : Q_A a0 p0,
        c_desc_idsys_ind Q_A e_Q q0 a0 p0 = q0).

    (** Kraus-von Raumer induction induces an identity system structure on [c_bundle_descent]. *)
    Local Instance idsys_c_bundle_descent : @IsIdentitySystem _ (coeq a0) c_bundle_descent p0.
    Proof.
      snrapply Build_IsIdentitySystem.
      - intros Q q0 x p.
        snrapply c_descentfam_sect.
        + exact (c_desc_idsys_ind (c_descentfam_A Q) (@c_descentfam_e Q) q0).
        + apply c_glue_desc_idsys_ind.
      - intros Q q0; cbn.
        nrapply c_desc_idsys_ind_beta.
    Defined.

    Definition c_bundle_descent_equiv_path (x : Coeq f g)
      : (coeq a0) = x <~> c_bundle_descent x
      := @equiv_transport_identitysystem (Coeq f g) (coeq a0) c_bundle_descent p0 _ x.

  End DescentIdSys.
End DescentCoeq.
