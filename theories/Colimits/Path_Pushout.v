Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Arrow Types.Forall Types.Sigma Cubical.DPath.
Require Import Homotopy.IdentitySystems.
Require Import Colimits.Pushout.

(** * Characterization of identity types of pushouts *)

(** A pointed type family over a pushout has an identity system structure precisely when its associated descent data satisfies Kraus and von Raumer's induction principle, https://arxiv.org/pdf/1901.06022.  *)
Section DescentPO.

  (** Assume there's a span diagram [A] <- [R] -> [B]. *)
  Context `{Univalence} {A B R : Type} (f : R -> A) (g : R -> B).

  (** Descent data over [A], [B], and [R], are type families [P_A : A -> Type] and [P_B : B -> Type], such that the fibers over [r : R] are equivalent, i.e. [P_A (f r) <~> P_B (g r)]. *)
  Context (P_A : A -> Type) (P_B : B -> Type)
    (e_P : forall r : R, P_A (f r) <~> P_B (g r)).

  (** The descent data bundles up to a type family over the pushout. *)
  Definition po_bundle_descent : forall (x : Pushout f g), Type.
  Proof.
    snrapply (Pushout_rec _ P_A P_B).
    intro r.
    by apply path_universe_uncurried.
  Defined.

  (** [transport] of [pglue r] over [po_bundle_descent] is given by [e_P]. *)
  Definition transport_pglue_bundle (r : R) (pa : P_A (f r))
    : transport po_bundle_descent (pglue r) pa = e_P r pa.
  Proof.
    nrapply transport_path_universe'.
    nrapply Pushout_rec_beta_pglue.
  Defined.

  Section DepDescentWFamily.

    (** Consider a dependent type family over [Pushout f g] and [po_bundle_descent]. *)
    Context (Q : forall x : Pushout f g, po_bundle_descent x -> Type).

    (** The associated dependent descent data of [Q] is given by the maps: *)
    Definition po_descentfam_A (a : A) (pa : P_A a) : Type
      := Q (pushl a) pa.

    Definition po_descentfam_B (b : B) (pb : P_B b) : Type
      := Q (pushr b) pb.

    Definition po_descentfam_e (r : R) {pa : P_A (f r)}
      : po_descentfam_A (f r) pa <~> po_descentfam_B (g r) (e_P r pa)
      := equiv_transportDD po_bundle_descent Q (pglue r)
        (transport_pglue_bundle r pa).

    (** A section of the dependent descent data are sections [f_A] and [f_B], with coherences [e_f]. *)
    Context (f_A : forall a : A, forall pa : P_A a, po_descentfam_A a pa)
      (f_B : forall b : B, forall pb : P_B b, po_descentfam_B b pb)
      (e_f : forall r : R, forall pa : P_A (f r),
        po_descentfam_e r (f_A (f r) pa) = f_B (g r) (e_P r pa)).

    (** Transporting in [Q] along [pglue] maps [f_A] to [f_B]. *)
    Definition pglue_descentfam_sect (r : R)
      : transport (fun x => forall px : po_bundle_descent x, Q x px)
        (pglue r) (f_A (f r)) = f_B (g r).
    Proof.
      apply dpath_forall.
      intro pa; simpl in pa.
      apply (equiv_inj (transport _ (transport_pglue_bundle r pa))).
      rhs snrapply (apD _ (transport_pglue_bundle r pa)).
      nrapply e_f.
    Defined.

    (** The section of dependent descent data bundles to a genuine section on the total space. *)
    Definition po_descentfam_sect
      : forall x : Pushout f g, forall px : po_bundle_descent x, Q x px
      := Pushout_ind _ f_A f_B pglue_descentfam_sect.

    Definition po_descentfam_sect_beta_pglue (r : R)
      : apD po_descentfam_sect (pglue r) = pglue_descentfam_sect r
      := Pushout_ind_beta_pglue _ f_A f_B pglue_descentfam_sect r.

  End DepDescentWFamily.

  Section DescentIdSys.

    (** Assume only [A] and [P_A] are pointed. There is an analogous statement where [B] and [P_B] is pointed. *)
    Context (a0 : A) (pa0 : P_A a0).

    (** Assume that the descent data ([P_A, P_B, e_P]) satisfies Kraus-von Raumer induction. *)
    Context (po_desc_A_idsys_ind : forall Q_A : (forall a : A, P_A a -> Type),
        forall Q_B : (forall b : B, P_B b -> Type),
        forall e_Q : (forall r : R, forall pa : P_A (f r),
          Q_A (f r) pa <~> Q_B (g r) (e_P r pa)),
        forall q0 : Q_A a0 pa0,
        forall a : A, forall pa : P_A a, Q_A a pa)
      (po_desc_B_idsys_ind : forall Q_A : (forall a : A, P_A a -> Type),
        forall Q_B : (forall b : B, P_B b -> Type),
        forall e_Q : (forall r : R, forall pa : P_A (f r),
          Q_A (f r) pa <~> Q_B (g r) (e_P r pa)),
        forall q0 : Q_A a0 pa0,
        forall b : B, forall pb : P_B b, Q_B b pb)
      (pglue_desc_idsys_ind : forall Q_A : (forall a : A, P_A a -> Type),
        forall Q_B : (forall b : B, P_B b -> Type),
        forall e_Q : (forall r : R, forall pa : P_A (f r),
          Q_A (f r) pa <~> Q_B (g r) (e_P r pa)),
        forall q0 : Q_A a0 pa0,
        forall r : R, forall pa : P_A (f r),
          e_Q r pa (po_desc_A_idsys_ind Q_A Q_B e_Q q0 (f r) pa)
          = po_desc_B_idsys_ind Q_A Q_B e_Q q0 (g r) (e_P r pa))
      (po_desc_idsys_ind_beta : forall Q_A : (forall a : A, P_A a -> Type),
        forall Q_B : (forall b : B, P_B b -> Type),
        forall e_Q : (forall r : R, forall pa : P_A (f r),
          Q_A (f r) pa <~> Q_B (g r) (e_P r pa)),
        forall q0 : Q_A a0 pa0,
          po_desc_A_idsys_ind Q_A Q_B e_Q q0 a0 pa0 = q0).

    (** Kraus-von Raumer induction on descent data induces an identity system structure on the total space. *)
    Local Instance isidsys_po_bundle_descent : @IsIdentitySystem _ (pushl a0) po_bundle_descent pa0.
    Proof.
      snrapply Build_IsIdentitySystem.
      - intros Q q0 x px.
        snrapply po_descentfam_sect.
        + nrapply po_desc_A_idsys_ind.
          * exact (po_descentfam_e Q).
          * exact q0.
        + nrapply po_desc_B_idsys_ind.
          * exact (po_descentfam_e Q).
          * exact q0.
        + apply pglue_desc_idsys_ind.
      - intros Q q0; cbn.
        nrapply po_desc_idsys_ind_beta.
    Defined.

    Definition po_bundle_descent_equiv_path (x : Pushout f g)
      : pushl a0 = x <~> po_bundle_descent x
      := @equiv_transport_identitysystem _ _ _ _ _ _.

  End DescentIdSys.
End DescentPO.
