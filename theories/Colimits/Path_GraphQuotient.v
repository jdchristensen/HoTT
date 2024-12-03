Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Forall Types.Arrow Types.Sigma.
Require Import Homotopy.IdentitySystems.
Require Import Colimits.GraphQuotient.

(** TODO: Move to PathGroupoids.v *)
Definition transportD_const {A : Type} (B : A -> Type) (C : Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C)
  : transportD B (fun _ _ => C) p y z = z.
Proof.
  by destruct p.
Defined.

Definition transportDD_const {A : Type} (B : A -> Type) (C : Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  (c1 : C)
  : transportDD B (fun _ _ => C) pA pB c1 = c1.
Proof.
  by destruct pB, pA.
Defined.

(** TODO: put in Sigma.v, after transportD_is_transport. *)
Definition transportDD_is_transport {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  (c1 : C a1 b1)
  : transportDD B C pA pB c1 = transport (fun (ab : sig B) => C ab.1 ab.2) (path_sigma' _ pA pB) c1.
Proof.
  by destruct pB, pA.
Defined.

(** * Characterization of identity types of graph quotients *)

(** A pointed type family over a graph quotient has an identity system structure precisely when its associated descent data satisfies Kraus and von Raumer's induction principle, https://arxiv.org/pdf/1901.06022. *)
Section DescentGQ.

  (** Consider a graph [A] with arrows [R]. *)
  Context `{Univalence} {A : Type} (R : A -> A -> Type).

  (** Descent data over [A] and [R] is a type family [P_A : A -> Type], such that if [a b : A] is related by [r : R a b], then the fibers [P_A a] and [P_A b] are equivalent, witnessed by [e_P]. *)
  Context (P_A : A -> Type) (e_P : forall a b : A, R a b -> P_A a <~> P_A b).

  (** The first two arguments of [e_P] are taken to be implicit. *)
  Arguments e_P {_ _} _.

  (** The descent data bundles up to a type family over [GraphQuotient R]. *)
  Definition gq_bundle_descent : GraphQuotient R -> Type.
  Proof.
    snrapply (GraphQuotient_rec P_A).
    intros a b r.
    exact (path_universe_uncurried (e_P r)).
  Defined.

  (** [transport] of [gqglue r] over [gq_bundle_descent] is given by [e_P]. *)
  Definition transport_gqglue_bundle {a b : A} (r : R a b) (pa : P_A a)
    : transport gq_bundle_descent (gqglue r) pa = e_P r pa.
  Proof.
    nrapply transport_path_universe'.
    nrapply GraphQuotient_rec_beta_gqglue.
  Defined.

  Section DependentDescentWithFamily.

    (* TODO: replace the material in GraphQuotient.v with this version. But maybe switch to the terminology used there? *)

    (** In this Section, we prove the analog of Lemma 6.12.4 from the book, which states that the total space [sig gq_bundle_descent] has the expected dependent induction principle.  The proof here is simpler than in the book. *)

    (** Consider a dependent type family over [GraphQuotient R] and [gq_bundle_descent]. This is a curried form of a type family over [sig gq_bundle_descent]. *)
    Context (Q : forall x : GraphQuotient R, gq_bundle_descent x -> Type).

    (** The dependent descent data is given by the following maps. *)
    Definition gq_descentfam_A (a : A) (pa : P_A a) : Type := Q (gq a) pa.

    Definition gq_descentfam_e {a b : A} (r : R a b) {pa : P_A a}
      : gq_descentfam_A a pa <~> gq_descentfam_A b (e_P r pa)
      := equiv_transportDD gq_bundle_descent Q (gqglue r) (transport_gqglue_bundle r pa).

    (** A section of the dependent descent data is given by a section [f_A], together with coherences [e_f]. *)
    Context (f_A : forall a : A, forall pa : P_A a, gq_descentfam_A a pa)
      (e_f : forall a b : A, forall r :  R a b, forall pa : P_A a,
          gq_descentfam_e r (f_A a pa) = f_A b (e_P r pa)).

    (** The first two arguments of [e_f] are taken to be implicit. *)
    Arguments e_f {_ _} _ _.

    (** Transporting over [Q] along [gqglue] is evaluation at the other endpoint on an edge. *)
    Definition gqglue_descentfam_ind (a b : A) (r : R a b)
      : transport (fun x : GraphQuotient R => forall px : gq_bundle_descent x, Q x px)
          (gqglue r) (f_A a) = f_A b.
    Proof.
      apply dpath_forall.
      intro pa.
      (* Apply a transport to both sides of the equation: *)
      apply (equiv_inj (transport (gq_descentfam_A b) (transport_gqglue_bundle r pa))).
      (* The LHS is now the unfolded form of [transportDD], so [e_f] applies to it: *)
      lhs nrapply e_f.
      symmetry; apply apD.
    Defined.

    (** The section of dependent descent data bundles to a genuine section on the total space. *)
    Definition gq_descentfam_ind : forall x : GraphQuotient R, forall px : gq_bundle_descent x, Q x px
      := GraphQuotient_ind _ f_A gqglue_descentfam_ind.

    (** This is a partial computation rule, which only handles paths in the base. *)
    Definition gq_descentfam_ind_beta_gqglue (a b : A) (r : R a b)
      : apD gq_descentfam_ind (gqglue r) = gqglue_descentfam_ind a b r
      := GraphQuotient_ind_beta_gqglue _ f_A gqglue_descentfam_ind a b r.

  End DependentDescentWithFamily.

  Section Flattening.

    (** The total space [sig gq_bundle_descent] is itself a graph quotient, with these constructors. *)

    Definition gq_descentfam {a : A} (pa : P_A a) : sig gq_bundle_descent
      := (gq a; pa).

    Definition gqglue_descentfam {a b : A} {pa : P_A a} {pb : P_A b}
      (r : R a b) (pr : e_P r pa = pb)
      : (gq a; pa) = (gq b; pb) :> sig gq_bundle_descent.
    Proof.
      snrapply (path_sigma' _ (gqglue r)).
      lhs nrapply transport_gqglue_bundle.
      exact pr.
    Defined.

    (** It will be convenient to state the recursion principle that the total space [sig gq_bundle_descent x] satsifies. *)
    Definition gq_descentfam_rec (Q : Type) (f_A : forall (a : A), P_A a -> Q)
      (e_f : forall (a b : A) (r : R a b) (pa : P_A a), f_A a pa = f_A b (e_P r pa))
      : sig gq_bundle_descent -> Q.
    Proof.
      intros [x px]; revert x px.
      snrapply (gq_descentfam_ind _ f_A).
      simpl.
      intros a b r pa.
      lhs nrapply transportDD_const.
      apply e_f.
    Defined.

    (** And the corresponding computation rule. *)
    Definition gq_descentfam_rec_beta_gqglue (Q : Type) (f_A : forall (a : A), P_A a -> Q)
      (e_f : forall (a b : A) (r : R a b) (pa : P_A a), f_A a pa = f_A b (e_P r pa))
      {a b : A} {pa : P_A a} {pb : P_A b} (r : R a b) (pr : e_P r pa = pb)
      : ap (gq_descentfam_rec Q f_A e_f) (gqglue_descentfam r pr)
        = e_f a b r pa @ ap (f_A b) pr.
    Proof.
      destruct pr.
      cbn.
      unfold gqglue_descentfam.
      unfold gq_descentfam_rec.
      rewrite 2 concat_p1.
      lhs nrapply (ap_path_sigma _ _ (gqglue r) _).
      rewrite gq_descentfam_ind_beta_gqglue.
      cbn.
      unfold gqglue_descentfam_ind.
      (* This is a bit trickier than the situation for the original proof of flattening,
         since we defined gq_descentfam_rec using gq_descentfam_ind rather than using
         GraphQuotient_rec.  I wonder if we can prove a better computation rule for
         gq_descentfam_ind which we could use here instead of using ap_path_sigma?
         Or maybe there is another approach. *)
    Admitted.

    (* This is essentially the same as the existing proof. *)
    Definition equiv_gq_flatten
      : { x : GraphQuotient R & gq_bundle_descent x }
          <~> GraphQuotient (fun a b => {r : R a.1 b.1 & e_P r a.2 = b.2}).
    Proof.
      snrapply equiv_adjointify.
      - snrapply gq_descentfam_rec.
        + exact (fun a pa => gq (a; pa)).
        + intros a b r pa; cbn beta.
          apply gqglue; exact (r; 1).
      - snrapply GraphQuotient_rec.
        + intros [a pa]. exact (gq a; pa).
        + intros [a pa] [b pb] [r pr]; cbn in r, pr.
          exact (gqglue_descentfam r pr).
      - snrapply GraphQuotient_ind.
        + reflexivity.
        + simpl.
          intros [a pa] [b pb] [r pr]; cbn in r, pr.
          nrapply transport_paths_FFlr'; apply equiv_p1_1q.
          rewrite GraphQuotient_rec_beta_gqglue.
          lhs nrapply gq_descentfam_rec_beta_gqglue.
          destruct pr.
          apply concat_p1.
      - intros [x px]; revert x px.
        snrapply gq_descentfam_ind; cbn.
        + reflexivity.
        + intros a b r pa; cbn beta.
          rewrite transportDD_is_transport.
          nrapply transport_paths_FFlr'; apply equiv_p1_1q.
          rewrite (concat_p1 (transport_gqglue_bundle r pa))^.
          rewrite gq_descentfam_rec_beta_gqglue.
          rewrite concat_p1.
          exact (GraphQuotient_rec_beta_gqglue _ _ (a; pa) (b; _) (r; 1)).
    Defined.

  End Flattening.

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
    Local Instance idsys_gq_bundle_descent : @IsIdentitySystem _ (gq a0) gq_bundle_descent p0.
    Proof.
      snrapply Build_IsIdentitySystem.
      - intros Q q0 x p.
        snrapply gq_descentfam_ind.
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
