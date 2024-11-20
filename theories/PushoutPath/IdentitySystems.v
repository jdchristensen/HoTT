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
  Global Instance isequiv_transport_IsIdSys (R : A -> Type) (r0 : R a0) `{IsIdSys _ r0} 
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

  Definition equiv_transport_IsIdSys (R : A -> Type) (r0 : R a0) `{IsIdSys _ r0} (a : A) 
    : (a0 = a) <~> R a := Build_Equiv _ _ (fun p => transport R (y:=a) p r0) _.

End IdSys.

(** Transport over dependent type families that depends on identifications in both [A] and [B] *)
Definition transportDD {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  (c1 : C a1 b1) : C a2 b2
  := transport (C a2) pB (transportD B C pA b1 c1).

(** Lemmata that will be useful to specify homotopies for the inverse. *)
Definition transportDD_concat {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 a3 : A} (pA1 : a1 = a2) (pA2 : a2 = a3)
  {b1 : B a1} {b2 : B a2} {b3 : B a3} (pB1 : transport B pA1 b1 = b2) (pB2 : transport B pA2 b2 = b3)
  (c1 : C a1 b1) 
  : transportDD B C (pA1 @ pA2) (transport_pp B pA1 pA2 b1 @ ap (transport B pA2) pB1 @ pB2) c1
  =  transportDD B C pA2 pB2 (transportDD B C pA1 pB1 c1).
Proof.
  by destruct pB2, pB1, pA2, pA1.
Defined.

(** This needs a new name *)
Definition lemma1 {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  : transport_pp B pA^ pA b2 @ ap (transport B pA) (moveL_transport_V B pA b1 b2 pB)^ 
  = ap (fun x => transport B x b2) (concat_Vp pA) @ pB^.
Proof.
  by destruct pB, pA.
Defined.

(** [transportDD] is an equivalence *)
Global Instance isequiv_transportDD 
  {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  : IsEquiv (transportDD B C pA pB).
Proof.
  snrapply isequiv_adjointify.
  1: {
    apply (transportDD B C pA^). 
    exact (moveL_transport_V B pA b1 b2 pB)^. }
  all: by destruct pB, pA. (* This will be very hairy to untangle. It is probably smart to control the homotopies better, but I don't know the pay-off if every function I use will be defined using destruct. *)
Defined.

Definition equiv_transportDD
  {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} {b2 : B a2} (pB : transport B pA b1 = b2)
  : C a1 b1 <~> C a2 b2
  := Build_Equiv _ _ (transportDD B C pA pB) _.

(** Since [transportD B C p] is definitionally [transportDD B C p 1], we get this as a special case. *)
Global Instance isequiv_transportD {A : Type} (B : A -> Type) 
  (C : forall a : A, B a -> Type) {x1 x2 : A} (p : x1 = x2) (y : B x1) 
  : IsEquiv (transportD B C p y).
Proof.
  snrapply Build_IsEquiv.
  { refine (_ o transportD B C p^ (transport B p y)).
    exact (transport (C x1) (transport_Vp _ p y)). }
  all: by destruct p.
Defined.

Definition equiv_transportD {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {a1 a2 : A} (pA : a1 = a2)
  {b1 : B a1} : C a1 b1 <~> C a2 (transport B pA b1)
  := equiv_transportDD B C pA 1.

(** Dependent application of two variables. We write [apDDKNM], where K is the application of a K-path between functions, to N- and M-paths between elements.  *)
Definition apDD011 {A : Type} (B : A -> Type) (C : forall a, B a -> Type)
  (f : forall a : A, forall ba : B a, C a ba)
  {a1 a2 : A} (pA : a1 = a2) 
  {ba1 : B a1} {ba2 : B a2} (pB : transport B pA ba1 = ba2)
  : transportDD B C pA pB (f a1 ba1) = f a2 ba2.
Proof.
  by destruct pB, pA.
Defined.

Definition apDD010 {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type) 
  (f : forall a : A, forall ba : B a, C a ba) 
  {a1 a2 : A} (p : a1 = a2) (x : B a1) 
  : transportD B C p x (f a1 x) = f a2 (transport B p x).
Proof.
  by destruct p.
Defined.

Definition apDD001 {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  (f : forall a : A, forall ba : B a, C a ba)
  {a : A} {b1 b2 : B a} (q : b1 = b2)
  : transport (C a) q (f a b1) = f a b2.
Proof.
  by destruct q .
Defined.

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

(** Considering a graph [A] with arrows given by [R], we will define sections of dependent descent data of the graph quotient. *)
(** Possible clean-ups. We can define type families with descent, and prove that for fixed descent data, the type of all type families with descent is contractible. This should be straight forward from the flattening lemma. *)
Section DescentGQ.
  Context `{Univalence} {A : Type} (R : A -> A -> Type).

  (** Descent data over [A] and [R] is a type family [P_A : A -> Type], such that if [a b : A] is related by [r : R a b], then the fibers [P_A a] and [P_A b] are equivalent. *)
  Context (P_A : A -> Type) (e_P : forall a b : A, R a b -> P_A a <~> P_A b).

  (** We make the first two arguments of [e_P] implicit. *)
  Arguments e_P {_ _} _.

  (** The descent data bundles up to a type family of [GraphQuotient R]. *)
  Definition bundle_descent : GraphQuotient R -> Type.
  Proof.
    snrapply GraphQuotient_rec.
    - exact P_A.
    - intros a b r.
      exact (path_universe_uncurried (e_P r)).
  Defined.

  (** [transport] of [gqglue r] over [bundle_descent] is given by [e_P]. *)
  Definition transport_gqglue_bundle {a b : A} (r : R a b) (pa : P_A a) : transport bundle_descent (gqglue r) pa = e_P r pa 
    := transport_path_universe' _ (gqglue r) (e_P r) (GraphQuotient_rec_beta_gqglue _ _ _ _ _) pa.

  Section DependentDescentGQ.
    (** The flattening lemma now tells us that the total space of [bundle_descent] is akin to a flattened graph quotient. From this perspective, we define dependent descent data as uncurried descent data of the total space of [bundle_descent] *)
    Context (Q_A : forall a : A, P_A a -> Type)
      (e_Q : forall a b : A, forall r : R a b, forall pa : P_A a, Q_A a pa <~> Q_A b (e_P r pa)).

    (** We make the first two arguments, and the last argument of [e_Q] implicit. *)
    Arguments e_Q {_ _} _ {_}.

    (** We transform [e_Q] to a form that can be used in [GraphQuotient_ind]. *)
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

    (** We can bundle up the descent data to a type family indexed over the graph quotient. *)
    Definition uncurry_bundle_dep_descent : forall x : GraphQuotient R, bundle_descent x -> Type 
    := GraphQuotient_ind _ Q_A glue_uncurry_bundle_dep_descent.

    (** [transportDD] over this bundle is given på [e_Q]. *)
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


    Section DescentSection.
      (** A dependent section of [Q] is given by a section [f_A] indexed over the total space of [P_A] and coherences [e_f]. *)
      Context (f_A : forall a : A, forall pa : P_A a, Q_A a pa)
        (e_f : forall a b : A, forall r :  R a b, forall pa : P_A a, e_Q r (f_A a pa) = f_A b (e_P r pa)).

      Arguments e_f {_ _} _ _.

      (** We transform [e_f] to a form that can be used by [GraphQuotient_ind]. *)
      Definition glue_bundle_section (a b : A) (r : R a b) : transport (fun x : GraphQuotient R => forall px : bundle_descent x, uncurry_bundle_dep_descent x px) (gqglue r) (f_A a) = f_A b.
      Proof.
        apply dpath_forall.
        intro pa.
        apply (equiv_inj (transport (Q_A b) (transport_gqglue_bundle r pa))).
        lhs nrapply transportDD_gqglue_bundle.
        rhs nrapply (apD (f_A b) (transport_gqglue_bundle r pa)).
        exact (e_f r pa).
      Defined.

      (** Using [f_A] and [e_f], we define a section of [uncurry_bundle_dep_descent]. *)
      Definition bundle_section : forall x : GraphQuotient R, forall px : bundle_descent x, uncurry_bundle_dep_descent x px
        := GraphQuotient_ind _ f_A glue_bundle_section.

      (** Alias to get the beta rule associated to [GraphQuotient_ind] *)
      Definition bundle_section_beta_ap (a b : A) (r :  R a b) 
        := GraphQuotient_ind_beta_gqglue _ f_A glue_bundle_section a b r.

      (** Alias to get the beta rule associated to [GraphQuotient_ind] *)
      Definition bundle_section_beta (a1 a2 : A) (r : R a1 a2) (p1 : P_A a1) 
        : bundle_section (gq a2) (e_P r p1) = e_Q r (bundle_section (gq a1) p1) 
        := (e_f r p1)^.

    End DescentSection.
  End DependentDescentGQ.

  Section DependentDescentWithFamily.
    (** We assume that we have a type family over the total space of the descent data over. *)
    Context (Q : forall x : GraphQuotient R, bundle_descent x -> Type).

    (** We can recover dependent descent data for this type family. *)
    Definition descent_family_A (a : A) (pa : P_A a) : Type := Q (gq a) pa.

    Definition descent_family_e {a b : A} (r : R a b) {pa : P_A a} : descent_family_A a pa <~> descent_family_A b (e_P r pa)
    := equiv_transportDD bundle_descent Q (gqglue r) (transport_gqglue_bundle r pa). 

    Context (f_A : forall a : A, forall pa : P_A a, descent_family_A a pa)
      (e_f : forall a b : A, forall r :  R a b, forall pa : P_A a, descent_family_e r (f_A a pa) = f_A b (e_P r pa)).

    Arguments e_f {_ _} _ _.

    Definition glue_descent_family_section (a b : A) (r : R a b) 
     : transport (fun x : GraphQuotient R => forall px : bundle_descent x, Q x px) (gqglue r) (f_A a) = f_A b.
    Proof.
      apply dpath_forall.
      intro pa.
      apply (equiv_inj (transport (descent_family_A b) (transport_gqglue_bundle r pa))).
      rhs nrapply (apD (f_A b) (transport_gqglue_bundle r pa)).
      exact (e_f r pa).
    Defined.

    Definition descent_family_section : forall x : GraphQuotient R, forall px : bundle_descent x, Q x px
      := GraphQuotient_ind _ f_A glue_descent_family_section.

    Definition descent_family_section_beta (a1 a2 : A) (r : R a1 a2) (p1 : P_A a1)
      : descent_family_section (gq a2) (e_P r p1) = descent_family_e r (descent_family_section (gq a1) p1)
      := (e_f r p1)^.

    Definition descent_family_section_beta_ap (a1 a2 : A) (r : R a1 a2) 
      := GraphQuotient_ind_beta_gqglue _ f_A glue_descent_family_section a1 a2 r. 

  End DependentDescentWithFamily.

  Section DescentIdSys.
    (** Assume [A] and [P_A] are pointed types. *)
    Context {a0 : A} {p0 : P_A a0}. 

    (** Assume for any pointed dependent descent data [Q_A], [e_Q], and [q0] that there are sections from the pointed descent data [P_A], [e_P], and [p0]. *)
    Context (desc_id_sys_ind : forall Q_A : forall a : A, P_A a -> Type, 
        forall e_Q : forall a b : A, forall r : R a b, forall pa : P_A a, Q_A a pa <~> Q_A b (e_P r pa),
        forall q0 : Q_A a0 p0, 
        forall a : A, forall pa : P_A a, Q_A a pa)
      (e_desc_id_sys_ind : forall Q_A : forall a : A, P_A a -> Type, 
        forall e_Q : forall a b : A, forall r : R a b, forall pa : P_A a, Q_A a pa <~> Q_A b (e_P r pa),
        forall q0 : Q_A a0 p0, forall a b : A, forall r :  R a b, forall pa : P_A a, 
        e_Q a b r pa (desc_id_sys_ind Q_A e_Q q0 a pa) = desc_id_sys_ind Q_A e_Q q0 b (e_P r pa))
      (desc_id_sys_ind_beta : forall Q_A : forall a : A, P_A a -> Type, 
        forall e_Q : forall a b : A, forall r : R a b, forall pa : P_A a, Q_A a pa <~> Q_A b (e_P r pa),
        forall q0 : Q_A a0 p0, 
        desc_id_sys_ind Q_A e_Q q0 a0 p0 = q0).


    (** Kraus-von Raumer induction can now be phrased as the pointed descent data [P_A], [e_P], and [p0] inducing an identity system structure on bundle_descent. *)
    Local Instance IsIdSys_bundle_descent : @IsIdSys _ (gq a0) bundle_descent p0.
    Proof.
      snrapply Build_IsIdSys.
      - intros Q q0 x p.
        pose (f_A := desc_id_sys_ind (descent_family_A Q) (@descent_family_e Q) q0).
        pose (e_f := e_desc_id_sys_ind (descent_family_A Q) (@descent_family_e Q) q0).
        exact (descent_family_section Q f_A e_f x p).
      - intros Q q0; cbn.
        exact (desc_id_sys_ind_beta (descent_family_A Q) (@descent_family_e Q) q0).
    Defined.

    Definition the_equivalence_that_will_save_my_life (x : GraphQuotient R) 
      : (gq a0) = x <~> bundle_descent x
      := @equiv_transport_IsIdSys (GraphQuotient R) (gq a0) bundle_descent p0 _ x.

  End DescentIdSys.
End DescentGQ.
