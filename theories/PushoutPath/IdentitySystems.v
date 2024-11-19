Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Colimits.GraphQuotient.

(** [transportD] is an equivalence *)
Definition isequiv_transportD {A : Type} (B : A -> Type) 
  (C : forall a : A, B a -> Type) {x1 x2 : A} (p : x1 = x2) (y : B x1) 
  : IsEquiv (transportD B C p y).
Proof.
  snrapply isequiv_adjointify; destruct p.
  - exact idmap.
  - reflexivity.
  - reflexivity.
Defined.

(** The true transport over dependent type families *)
Definition transportDD {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  (c1 : C a1 b1) : C a2 b2.
Proof.
  by destruct pB, pA.
Defined.

(** [transport] and [transportD] is enough to do [transportDD] *)
(** TODO: Because this is definitional, the conclusion here should be taken to be the *definition* of transportDD. *)
Definition transport_transportD_transportDD {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  (c1 : C a1 b1) : transport (C a2) pB (transportD B C pA b1 c1) = transportDD B C pA pB c1.
Proof.
  reflexivity.
Defined.

(** Lemma 6.12.1 for transportDD *)
Definition transportDD_path_universe' `{Univalence} {A : Type} (B : A -> Type) 
  (C : forall a : A, B a -> Type) {a1 a2 : A} (p : a1 = a2) 
  (b1 : B a1) (b2 : B a2) (q : transport B p b1 = b2) 
  (f : C a1 b1 <~> C a2 b2) 
  (r : ((dpath_arrow B (fun _ => Type) p (C a1) (C a2))^-1 (apD C p) b1) @ (ap (fun x => C a2 x) q) = (transport_const p (C a1 b1)) @ path_universe f) 
  (c1 : C a1 b1)
  : transportDD B C p q c1 = f c1.
Proof.
  apply moveR_Vp in r.
  (* If the statement is changed to use [path_universe_uncurried], then the next line isn't needed. *)
  change (path_universe f) with (path_universe_uncurried f) in r.
  apply moveR_equiv_V in r.
  destruct r.
  by destruct p, q.
Defined.

(** We first prove Theorem 5.8.2. (i) => (iii) *)
Context {A : Type} (a0 : A).

(** Start to reason about graph quotients over here *)
Context (R : A -> A -> Type). 

(** Descent data over a graph quotient is a type family over the graph [A], together with coherences for each relation [r : R a b] *)
Section DescentGQ.
  Context `{Univalence} (P_A : A -> Type) 
    (e_P : forall a b : A, R a b -> P_A a <~> P_A b).

  (** We're making the first two arguments of [e_P] implicit, as they can be inferred through the relation *)
  Arguments e_P {_ _} _.

  (** We can bundle up the descent data to a type family over the graph quotient *)
  Definition bundle_descent : GraphQuotient R -> Type.
  Proof.
    snrapply GraphQuotient_rec.
    - exact P_A.
    - intros a b r.
      snrapply path_universe.
      + exact (e_P r).
      + exact (equiv_isequiv (e_P r)).
  Defined.

  (** [transport] over this bundle is given by [e_P]*)
  Definition transport_gqglue_bundle {a b : A} (r : R a b) (pa : P_A a) : transport bundle_descent (gqglue r) pa = e_P r pa 
    := transport_path_universe' _ (gqglue r) (e_P r) (GraphQuotient_rec_beta_gqglue _ _ _ _ _) pa.

  (** The flattening lemma now tells us that the total space of [bundle_descent] is akin to a flattened graph quotient. From this perspective, we define dependent descent data as uncurried descent data of the total space of [bundle_descent] *)
  Section DependentDescentGQ.
    Context (Q_A : forall a : A, P_A a -> Type)
      (e_Q : forall a b : A, forall r : R a b, forall pa : P_A a, 
        Q_A a pa <~> Q_A b (e_P r pa)).

    Arguments e_Q {_ _} _ {_}.

    Definition glue_uncurry_bundle_dep_descent (a b : A) (r : R a b) 
      : transport (fun x : GraphQuotient R => bundle_descent x -> Type) 
      (gqglue r) (Q_A a) = Q_A b.
    Proof.
      apply (dpath_arrow bundle_descent (fun _ => Type) 
        (gqglue r) (Q_A a) (Q_A b)).
      intro pa.
      lhs snrapply transport_const.
      rhs snrapply (ap (fun x => Q_A b x) (transport_gqglue_bundle _ _)).
      snrapply path_universe.
      + exact (e_Q r).
      + exact (equiv_isequiv (e_Q r)).
    Defined.

    (** We can bundle up the descent data to a type family indexed over the graph quotient *)
    Definition uncurry_bundle_dep_descent : forall x : GraphQuotient R, bundle_descent x -> Type 
    := GraphQuotient_ind _ Q_A glue_uncurry_bundle_dep_descent.

    (** [transportDD] over this bundle is given på [e_Q]*)
    Definition transportDD_gqglue_bundle {a b : A} (r : R a b) (pa : P_A a) (qa : Q_A a pa) 
      : transportDD bundle_descent uncurry_bundle_dep_descent (gqglue r) (transport_gqglue_bundle r pa) qa = e_Q r qa.
    Proof.
      snrapply transportDD_path_universe'. cbn.
      rewrite (GraphQuotient_ind_beta_gqglue _ Q_A glue_uncurry_bundle_dep_descent _ _ r).
      unfold glue_uncurry_bundle_dep_descent.
      rewrite (eissect (dpath_arrow bundle_descent (fun _ => Type) (gqglue r) (Q_A a) (Q_A b)) _).
      lhs nrapply concat_pp_p.
      nrapply whiskerL.
      lhs nrapply concat_pp_p.
      lhs nrapply (idpath _ @@ concat_Vp (ap _ _)).
      snrapply concat_p1.
    Defined.

    (** A dependent section of [Q] is given by a section indexed over the total space of [P_A] and coherences *)
    Context (f_A : forall a : A, forall pa : P_A a, Q_A a pa)
      (e_f : forall a b : A, forall r :  R a b, forall pa : P_A a, e_Q r (f_A a pa) = f_A b (e_P r pa)).

    Arguments e_f {_ _} _ _.

    Definition bundle_section : forall x : GraphQuotient R, forall px : bundle_descent x, uncurry_bundle_dep_descent x px.
    Proof.
      snrapply GraphQuotient_ind.
      - exact f_A.
      - intros a b r.
        apply dpath_forall.
        intro pa.
        rapply (equiv_inj (transport (Q_A b) (transport_gqglue_bundle r pa))).
        rewrite (transport_transportD_transportDD bundle_descent uncurry_bundle_dep_descent (gqglue r)).
        rewrite transportDD_gqglue_bundle.
        rewrite (apD (f_A b) (transport_gqglue_bundle r pa)).
        exact (e_f r pa).
    Defined.

  End DependentDescentGQ.
End DescentGQ.

