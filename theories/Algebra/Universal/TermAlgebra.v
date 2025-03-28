(** This file defines the term algebra [TermAlgebra], also referred to as the absolutely free algebra.

    We show that term algebra forms an adjoint functor from the category of hset carriers

<<
      {C : Carrier σ | forall s, IsHSet (C s)}
>>

    to the category of algebras (without equations) [Algebra σ], where [Carriers σ] is notation for [Sort σ -> Type].  See [ump_term_algebra].

    There is a similar construction for algebras with equations, the free algebra [FreeAlgebra]. The free algebra is defined in another file. *)

Require Export HoTT.Algebra.Universal.Algebra.

Require Import
  HoTT.Universes.HSet
  HoTT.Classes.interfaces.canonical_names
  HoTT.Algebra.Universal.Homomorphism
  HoTT.Algebra.Universal.Congruence.

Unset Elimination Schemes.

Local Open Scope Algebra_scope.

(** The term algebra carriers are generated by [C : Carriers σ], with an element for each element of [C s], and an operation for each operation symbol [u : Symbol σ]. *)

Inductive CarriersTermAlgebra {σ} (C : Carriers σ) : Carriers σ :=
  | var_term_algebra : forall s, C s -> CarriersTermAlgebra C s
  | ops_term_algebra : forall (u : Symbol σ),
      DomOperation (CarriersTermAlgebra C) (σ u) ->
      CarriersTermAlgebra C (sort_cod (σ u)).

Scheme CarriersTermAlgebra_ind := Induction for CarriersTermAlgebra Sort Type.
Arguments CarriersTermAlgebra_ind {σ}.

Definition CarriersTermAlgebra_rect {σ} := @CarriersTermAlgebra_ind σ.

Definition CarriersTermAlgebra_rec {σ : Signature} (C : Carriers σ)
  (P : Sort σ -> Type) (vs : forall (s : Sort σ), C s -> P s)
  (os : forall (u : Symbol σ) (c : DomOperation (CarriersTermAlgebra C) (σ u)),
        (forall i : Arity (σ u), P (sorts_dom (σ u) i)) -> P (sort_cod (σ u)))
  (s : Sort σ) (T : CarriersTermAlgebra C s)
  : P s
  := CarriersTermAlgebra_ind C (fun s _ => P s) vs os s T.

(** A family of relations [R : forall s, Relation (C s)] can be extended to a family of relations on the term algebra carriers,

<<
      forall s, Relation (CarriersTermAlgebra C s)
>>

    See [ExtendDRelTermAlgebra] and [ExtendRelTermAlgebra] below. *)

Fixpoint ExtendDRelTermAlgebra {σ : Signature} {C : Carriers σ}
  (R : forall s, Relation (C s)) {s1 s2 : Sort σ}
  (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
  : Type
  := match S, T with
     | var_term_algebra s1 x, var_term_algebra s2 y =>
        {p : s1 = s2 | R s2 (p # x) y}
     | ops_term_algebra u1 a, ops_term_algebra u2 b =>
        { p : u1 = u2 |
          forall i : Arity (σ u1),
          ExtendDRelTermAlgebra
            R (a i) (b (transport (fun v => Arity (σ v)) p i))}
     | _, _ => Empty
     end.

Definition ExtendRelTermAlgebra {σ : Signature} {C : Carriers σ}
  (R : forall s, Relation (C s)) {s : Sort σ}
  : CarriersTermAlgebra C s -> CarriersTermAlgebra C s -> Type
  := ExtendDRelTermAlgebra R.

(** The next section shows, in particular, the following: If [R : forall s, Relation (C s)] is a family of mere equivalence relations, then [@ExtendRelTermAlgebra σ C R] is a family of mere equivalence relations. *)

Section extend_rel_term_algebra.
  Context `{Funext} {σ : Signature} {C : Carriers σ}
    (R : forall s, Relation (C s))
    `{!forall s, is_mere_relation (C s) (R s)}.

  #[export] Instance hprop_extend_drel_term_algebra {s1 s2 : Sort σ}
    (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
    : IsHProp (ExtendDRelTermAlgebra R S T).
  Proof.
    generalize dependent s2.
    induction S; intros s2 T; destruct T; exact _.
  Qed.

  #[export] Instance reflexive_extend_rel_term_algebra
    `{!forall s, Reflexive (R s)} {s : Sort σ}
    : Reflexive (@ExtendRelTermAlgebra σ C R s).
  Proof.
    intro S. induction S as [| u c h].
    - by exists idpath.
    - exists idpath. intro i. apply h.
  Qed.

  Lemma symmetric_extend_drel_term_algebra
    `{!forall s, Symmetric (R s)} {s1 s2 : Sort σ}
    (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
    (h : ExtendDRelTermAlgebra R S T)
    : ExtendDRelTermAlgebra R T S.
  Proof.
    generalize dependent s2.
    induction S as [| u c h]; intros s2 [] p.
    - destruct p as [p1 p2].
      induction p1. exists idpath. by symmetry.
    - elim p.
    - elim p.
    - destruct p as [p f].
      induction p. exists idpath. intro i. apply h. apply f.
  Qed.

  #[export] Instance symmetric_extend_rel_term_algebra
    `{!forall s, Symmetric (R s)} {s : Sort σ}
    : Symmetric (@ExtendRelTermAlgebra σ C R s).
  Proof.
    intros S T. apply symmetric_extend_drel_term_algebra.
  Defined.

  Lemma transitive_extend_drel_term_algebra
    `{!forall s, Transitive (R s)} {s1 s2 s3 : Sort σ}
    (S : CarriersTermAlgebra C s1)
    (T : CarriersTermAlgebra C s2)
    (U : CarriersTermAlgebra C s3)
    (h1 : ExtendDRelTermAlgebra R S T)
    (h2 : ExtendDRelTermAlgebra R T U)
    : ExtendDRelTermAlgebra R S U.
  Proof.
    generalize dependent s3.
    generalize dependent s2.
    induction S as [| u c h];
      intros s2 [? d | ? d] h2 s3 [] h3;
      destruct h2 as [p2 P2], h3 as [p3 P3] || by (elim h2 || elim h3).
    - exists (p2 @ p3).
      rewrite transport_pp.
      induction p2, p3.
      by transitivity d.
    - exists (p2 @ p3).
      intro i.
      induction p2.
      apply (h i _ (d i)).
      + apply P2.
      + rewrite concat_1p. apply P3.
  Qed.

  #[export] Instance transitive_extend_rel_term_algebra
    `{!forall s, Transitive (R s)} {s : Sort σ}
    : Transitive (@ExtendRelTermAlgebra σ C R s).
  Proof.
    intros S T U. apply transitive_extend_drel_term_algebra.
  Defined.

  #[export] Instance equivrel_extend_rel_term_algebra
    `{!forall s, EquivRel (R s)} (s : Sort σ)
    : EquivRel (@ExtendRelTermAlgebra σ C R s).
  Proof.
    constructor; exact _.
  Qed.

End extend_rel_term_algebra.

(** By using path (propositional equality) as equivalence relation for [ExtendRelTermAlgebra], we obtain an equivalent notion of equality of term algebra carriers, [equiv_path_extend_path_term_algebra]. The reason for introducing [ExtendRelTermAlgebra] is to have a notion of equality which works well together with induction on term algebras. *)

Section extend_path_term_algebra.
  Context `{Funext} {σ} {C : Carriers σ} `{!forall s, IsHSet (C s)}.

  Definition ExtendPathTermAlgebra {s : Sort σ}
    (S : CarriersTermAlgebra C s) (T : CarriersTermAlgebra C s)
    : Type
    := ExtendRelTermAlgebra (fun s => paths) S T.

  #[export] Instance reflexive_extend_path_term_algebra
    : forall s : Sort σ, Reflexive (@ExtendPathTermAlgebra s).
  Proof.
    by apply reflexive_extend_rel_term_algebra.
  Defined.

  Lemma reflexive_extend_path_term_algebra_path {s : Sort σ}
    {S T : CarriersTermAlgebra C s} (p : S = T)
    : ExtendPathTermAlgebra S T.
  Proof.
    induction p. apply reflexive_extend_path_term_algebra.
  Defined.

  #[export] Instance symmetric_extend_path_term_algebra
    : forall s : Sort σ, Symmetric (@ExtendPathTermAlgebra s).
  Proof.
    apply symmetric_extend_rel_term_algebra. intros s x y. exact inverse.
  Defined.

  #[export] Instance transitive_extend_path_term_algebra
    : forall s : Sort σ, Transitive (@ExtendPathTermAlgebra s).
  Proof.
    apply transitive_extend_rel_term_algebra. intros s x y z. exact concat.
  Defined.

  #[export] Instance equivrel_extend_path_term_algebra
    : forall s : Sort σ, EquivRel (@ExtendPathTermAlgebra s).
  Proof.
    constructor; exact _.
  Qed.

  #[export] Instance hprop_extend_path_term_algebra (s : Sort σ)
    : is_mere_relation (CarriersTermAlgebra C s) ExtendPathTermAlgebra.
  Proof.
    intros S T. exact _.
  Defined.

  Lemma dependent_path_extend_path_term_algebra {s1 s2 : Sort σ}
    (S : CarriersTermAlgebra C s1) (T : CarriersTermAlgebra C s2)
    (e : ExtendDRelTermAlgebra (fun s => paths) S T)
    : {p : s1 = s2 | p # S = T}.
  Proof.
    generalize dependent s2.
    induction S as [| u c h];
        intros s2 [? d | ? d] e;
        solve [elim e] || destruct e as [p e].
    - exists p. by induction p, e.
    - induction p. exists idpath. cbn. f_ap. funext a.
      destruct (h a _ (d a) (e a)) as [p q].
      by induction (hset_path2 idpath p).
  Defined.

  Lemma path_extend_path_term_algebra {s : Sort σ}
    (S T : CarriersTermAlgebra C s) (e : ExtendPathTermAlgebra S T)
    : S = T.
  Proof.
    destruct (dependent_path_extend_path_term_algebra S T e) as [p q].
    by induction (hset_path2 idpath p).
  Defined.

  #[export] Instance hset_carriers_term_algebra (s : Sort σ)
    : IsHSet (CarriersTermAlgebra C s).
  Proof.
    apply (@ishset_hrel_subpaths _ ExtendPathTermAlgebra).
    - apply reflexive_extend_path_term_algebra.
    - apply hprop_extend_path_term_algebra; exact _.
    - exact path_extend_path_term_algebra.
  Defined.

  Definition equiv_path_extend_path_term_algebra {s : Sort σ}
    (S T : CarriersTermAlgebra C s)
    : ExtendPathTermAlgebra S T <~> (S = T)
    := equiv_iff_hprop
        (path_extend_path_term_algebra S T)
        reflexive_extend_path_term_algebra_path.

End extend_path_term_algebra.

(** At this point we can define the term algebra. *)

Definition TermAlgebra `{Funext} {σ : Signature}
  (C : Carriers σ) `{!forall s, IsHSet (C s)}
  : Algebra σ
  := Build_Algebra (CarriersTermAlgebra C) (@ops_term_algebra _ C).

Lemma isinj_var_term_algebra {σ} (C : Carriers σ) (s : Sort σ) (x y : C s)
  : var_term_algebra C s x = var_term_algebra C s y -> x = y.
Proof.
  intro p.
  apply reflexive_extend_path_term_algebra_path in p.
  destruct p as [p1 p2].
  by destruct (hset_path2 p1 idpath)^.
Qed.

Lemma isinj_ops_term_algebra `{Funext} {σ} (C : Carriers σ)
  (u : Symbol σ) (a b : DomOperation (CarriersTermAlgebra C) (σ u))
  : ops_term_algebra C u a = ops_term_algebra C u b -> a = b.
Proof.
  intro p.
  apply reflexive_extend_path_term_algebra_path in p.
  destruct p as [p1 p2].
  destruct (hset_path2 p1 idpath)^.
  funext i.
  apply path_extend_path_term_algebra.
  apply p2.
Qed.

(** The extension [ExtendRelTermAlgebra R], of a family of mere
    equivalence relations [R], is a congruence. *)

#[export] Instance is_congruence_extend_rel_term_algebra
  `{Funext} {σ} (C : Carriers σ) `{!forall s, IsHSet (C s)}
  (R : forall s, Relation (C s)) `{!forall s, EquivRel (R s)}
  `{!forall s, is_mere_relation (C s) (R s)}
  : IsCongruence (TermAlgebra C) (@ExtendRelTermAlgebra σ C R).
Proof.
  constructor.
  - intros. exact _.
  - intros. exact _.
  - intros u a b c. exists idpath. intro i. apply c.
Defined.

(** Given and family of functions [f : forall s, C s -> A s], we can extend it to a [TermAlgebra C $-> A], as shown in the next section. *)

Section hom_term_algebra.
  Context
    `{Funext} {σ} {C : Carriers σ} `{!forall s, IsHSet (C s)}
    (A : Algebra σ) (f : forall s, C s -> A s).

  Definition map_term_algebra {σ} {C : Carriers σ} (A : Algebra σ)
    (f : forall s, C s -> A s) (s : Sort σ) (T : CarriersTermAlgebra C s)
    : A s
    := CarriersTermAlgebra_rec C A f (fun u _ r => u.#A r) s T.

  #[export] Instance is_homomorphism_map_term_algebra
    : @IsHomomorphism σ (TermAlgebra C) A (map_term_algebra A f).
  Proof.
    intros u a. by refine (ap u.#A _).
  Qed.

  Definition hom_term_algebra : TermAlgebra C $-> A
    := @Build_Homomorphism σ (TermAlgebra C) A (map_term_algebra A f) _.

End hom_term_algebra.

(** The next section proves the universal property of the term algebra,
    that [TermAlgebra] is a left adjoint functor

<<
      {C : Carriers σ | forall s, IsHSet (C s)} -> Algebra σ,
>>

    with right adjoint the forgetful functor. This is stated below as
    an equivalence

<<
      Homomorphism (TermAlgebra C) A <~> (forall s, C s -> A s),
>>

    given by precomposition with
    
<<
      var_term_algebra C s : C s -> TermAlgebra C s.
>>
*)

Section ump_term_algebra.
  Context
    `{Funext} {σ} (C : Carriers σ) `{forall s, IsHSet (C s)} (A : Algebra σ).

  (** By precomposing [Homomorphism (TermAlgebra C) A] with
      [var_term_algebra], we obtain a family [forall s, C s -> A s]. *)

  Definition precomp_var_term_algebra (f : TermAlgebra C $-> A)
    : forall s, C s -> A s
    := fun s x => f s (var_term_algebra C s x).

  Lemma path_precomp_var_term_algebra_to_hom_term_algebra
    : forall (f : TermAlgebra C $-> A),
      hom_term_algebra A (precomp_var_term_algebra f) = f.
  Proof.
    intro f.
    apply path_homomorphism.
    funext s T.
    induction T as [|u c h].
    - reflexivity.
    - refine (_ @ (is_homomorphism f u c)^).
      refine (ap u.#A _). funext i. apply h.
  Defined.

  Lemma path_hom_term_algebra_to_precomp_var_term_algebra
    : forall (f : forall s, C s -> A s),
      precomp_var_term_algebra (hom_term_algebra A f) = f.
  Proof.
    intro f. by funext s a.
  Defined.

  (** Precomposition with [var_term_algebra] is an equivalence *)

  #[export] Instance isequiv_precomp_var_term_algebra
    : IsEquiv precomp_var_term_algebra.
  Proof.
    srapply isequiv_adjointify.
    - apply hom_term_algebra.
    - intro. apply path_hom_term_algebra_to_precomp_var_term_algebra.
    - intro. apply path_precomp_var_term_algebra_to_hom_term_algebra.
  Defined.

  (** The universal property of the term algebra: The [TermAlgebra]
      is a left adjoint functor.
      Notice [isequiv_precomp_var_term_algebra] above. *)

  Theorem ump_term_algebra
    : (TermAlgebra C $-> A) <~> (forall s, C s -> A s).
  Proof.
    exact (Build_Equiv _ _ precomp_var_term_algebra _).
  Defined.

End ump_term_algebra.

