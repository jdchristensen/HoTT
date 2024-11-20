Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import Colimits.GraphQuotient.

Section IdSys.
  Context {A : Type} {a0 : A}.

  (** A pointed type family is an identity system if there is an instance of the following class. *)
  Class IsIdSys (R : A -> Type) (r0 : R a0)
    := {
      indIdSys (D : forall a : A, R a -> Type) (d : D a0 r0) (a : A) (r : R a) : D a r;
      beta_indIdSys (D : forall a : A, R a -> Type) (d : D a0 r0) : indIdSys D d a0 r0 = d
    }.

  (** Theorem 5.8.2. (i) => (iii) *)
  Definition isequiv_transport_IsIdSys (R : A -> Type) (r0 : R a0) `{IsIdSys _ r0} 
    (a : A) : IsEquiv (fun p => transport R (y:=a) p r0).
  Proof.
    pose (f := indIdSys (fun a _ => a0 = a) (idpath _)).
    pose (b := beta_indIdSys (fun a _ => a0 = a) (idpath _)).
    srapply isequiv_adjointify.
    - exact (f a).
    - intro r.
      exact ((indIdSys 
        (fun (a' : A) (r' : R a') => transport R (f a' r') r0 = r') 
        (ap (fun x => transport R x r0) b)) 
        a r).
    - by intros [].
  Defined.

  Definition equiv_transport_IsIdSys (R : A -> Type) (r0 : R a0) `{IsIdSys _ r0} (a : A) : (a0 = a) <~> R a.
  Proof.
    snrapply Build_Equiv.
    - exact (fun p => transport R (y:=a) p r0).
    - exact (isequiv_transport_IsIdSys _ _ _).
  Defined.

End IdSys.

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

(** Transport over dependent type families that depends on identifications in both [A] and [B] *)
Definition transportDD {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  (c1 : C a1 b1) : C a2 b2
  := transport (C a2) pB (transportD B C pA b1 c1).

(** Lemma 6.12.1 for transportDD *)
Definition transportDD_path_universe' `{Univalence} {A : Type} (B : A -> Type) 
  (C : forall a : A, B a -> Type) {a1 a2 : A} (p : a1 = a2) 
  (b1 : B a1) (b2 : B a2) (q : transport B p b1 = b2) 
  (f : C a1 b1 <~> C a2 b2) 
  (r : ((dpath_arrow B (fun _ => Type) p (C a1) (C a2))^-1 (apD C p) b1) @ (ap (fun x => C a2 x) q) = (transport_const p (C a1 b1)) @ path_universe_uncurried f)
  (c1 : C a1 b1)
  : transportDD B C p q c1 = f c1.
Proof.
  destruct p; cbn in *.
  apply cancelL in r.
  by apply transport_path_universe'.
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
      exact (path_universe_uncurried (e_P r)).
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
      exact (path_universe_uncurried (e_Q r)).
    Defined.

    (** We can bundle up the descent data to a type family indexed over the graph quotient *)
    Definition uncurry_bundle_dep_descent : forall x : GraphQuotient R, bundle_descent x -> Type 
    := GraphQuotient_ind _ Q_A glue_uncurry_bundle_dep_descent.

    (** [transportDD] over this bundle is given på [e_Q]*)
    Definition transportDD_gqglue_bundle {a b : A} (r : R a b) (pa : P_A a) (qa : Q_A a pa) 
      : transportDD bundle_descent uncurry_bundle_dep_descent (gqglue r) (transport_gqglue_bundle r pa) qa = e_Q r qa.
    Proof.
      snrapply transportDD_path_universe'; cbn.
      lhs nrapply (apD10 (ap (dpath_arrow _ _ (gqglue r) _ _)^-1 
        (GraphQuotient_ind_beta_gqglue _ _ glue_uncurry_bundle_dep_descent _ _ r)) _ @@ idpath).
      lhs nrapply (apD10 (eissect (dpath_arrow _ _ (gqglue r) _ _) _) _ @@ idpath).
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

    Definition glue_bundle_section (a b : A) (r : R a b) : transport (fun x : GraphQuotient R => forall px : bundle_descent x, uncurry_bundle_dep_descent x px) (gqglue r) (f_A a) = f_A b.
    Proof.
      apply dpath_forall.
      intro pa.
      apply (equiv_inj (transport (Q_A b) (transport_gqglue_bundle r pa))).
      lhs nrapply transportDD_gqglue_bundle.
      rhs nrapply (apD (f_A b) (transport_gqglue_bundle r pa)).
      exact (e_f r pa).
    Defined.

    Definition bundle_section : forall x : GraphQuotient R, forall px : bundle_descent x, uncurry_bundle_dep_descent x px
      := GraphQuotient_ind _ f_A glue_bundle_section.

    Definition bundle_section_beta_ap (a b : A) (r :  R a b) 
      := GraphQuotient_ind_beta_gqglue _ f_A glue_bundle_section a b r.

    Definition bundle_section_beta (a1 a2 : A) (r : R a1 a2) (p1 : P_A a1) 
      : bundle_section (gq a2) (e_P r p1) = e_Q r (bundle_section (gq a1) p1) 
      := (e_f r p1)^.

  End DependentDescentGQ.
End DescentGQ.

