(** * Injectivity for Sigma types and examples of Injective Types which use this setup *)

(** Many proofs guided by original Agda formalization in the Type Topology Library which can be found at: https://martinescardo.github.io/TypeTopology/InjectiveTypes.Sigma and InjectiveTypes.MathematicalStructuresMoreGeneral. *)

Require Import Basics.
Require Import Types.Forall Types.Sigma Types.Universe.
Require Import Modalities.ReflectiveSubuniverse.
Require Import Truncations.

Require Import InjectiveTypes.
Require Import TypeFamKanExt.

Section AlgFlabSigma.
  Context {X : Type} (A : X -> Type) (Xaf : IsAlgebraicFlabbyType X).

  Definition alg_flab_map
    (P : Type) (PropP : IsHProp P) (f : P -> X)
    : (A (Xaf _ _ f).1) -> (forall h, A (f h))
    := fun a h => (Xaf _ _ f).2 h # a.

  (** The condition for a sigma type over an algebraically flabby type can be described as the existence of a section to the preceding map. *)
  Definition alg_flab_sigma_condition : Type
    := forall P PropP f, {s : _ & ((alg_flab_map P PropP f) o s) == idmap}.

  (** A sigma type over an algebraically flabby type is also algebraically flabby, and thus algebraically injective, when the above condition holds. *)
  Definition alg_flab_sigma (cond : alg_flab_sigma_condition)
    : IsAlgebraicFlabbyType {x : X & A x}.
  Proof.
    intros P PropP f.
    pose (s := (cond P PropP (pr1 o f)).1).
    pose (e := (cond P PropP (pr1 o f)).2).
    srefine (((Xaf _ _ (pr1 o f)).1; s (pr2 o f)); _).
    intros h.
    srapply path_sigma.
    - apply ((Xaf _ _ (pr1 o f)).2 h).
    - apply (apD10 (e (pr2 o f)) h).
  Defined.

  Definition alg_inj_sigma (cond : alg_flab_sigma_condition)
    : IsAlgebraicInjectiveType {x : X & A x}
    := (alg_inj_alg_flab (alg_flab_sigma cond)).

End AlgFlabSigma.

(** Taking our algebraically flabby type [X] to be [Type], this introduces our primary examples (the type of pointed types, monoids, etc.), and introduces a few simplifying lemmas. *)
Section AlgFlabUniverse.
  Context (S : Type -> Type) (T : forall {X Y}, X <~> Y -> S X -> S Y) (Trefl : forall {X}, (T (equiv_idmap X) == idmap)).

  (** For a sigma type over [Type], the map [alg_flab_map] can be exchanged for either of these simpler maps for which an equivalent condition for algebraic injectivity can be defined. *)
  Definition alg_flab_map_forall `{Funext}
    (P : Type) (PropP : IsHProp P) (A : P -> Type)
    : S (forall h, A h) -> (forall h, S (A h)).
  Proof.
    intros s h.
    srefine (T (forall h, A h) _ _ s).
    apply (@equiv_contr_forall _ _ (contr_inhabited_hprop _ _)).
  Defined.

  Definition alg_flab_map_sigma
    (P : Type) (PropP : IsHProp P) (A : P -> Type)
    : S {h : P & A h} -> (forall h, S (A h)).
  Proof.
    intros s h.
    srefine (T _ _ _ s).
    apply (@equiv_contr_sigma _ _ (contr_inhabited_hprop _ _)).
  Defined.

  Definition alg_flab_sigma_condition_forall `{Funext} : Type
    := forall P PropP A, {s : _ & ((alg_flab_map_forall P PropP A) o s) == idmap}.

  Definition alg_flab_sigma_condition_sigma : Type
    := forall P PropP A, {s : _ & ((alg_flab_map_sigma P PropP A) o s) == idmap}.
  (** These can be though of as a closure condition under pi or sigma types for the type family [S]. *)

  Definition homotopic_alg_flab_map_alg_flab_map_forall `{Univalence}
    (P : Type) (PropP : IsHProp P) (A : P -> Type)
    : alg_flab_map_forall P PropP A == alg_flab_map S alg_flab_Type_forall P PropP A.
  Proof.
    intros s. apply path_forall. intros h.
    srefine (homotopic_trequiv S T (@univalent_transport H S) Trefl _ _ s).
    intros X.
    apply univalent_transport_idequiv.
  Defined.

  Definition homotopic_alg_flab_map_alg_flab_map_sigma `{Univalence}
    (P : Type) (PropP : IsHProp P) (A : P -> Type)
    : alg_flab_map_sigma P PropP A == alg_flab_map S alg_flab_Type_sigma P PropP A.
  Proof.
    intros s. apply path_forall. intros h.
    srefine (homotopic_trequiv S T (@univalent_transport H S) Trefl _ _ s).
    intros X.
    apply univalent_transport_idequiv.
  Defined.

  Definition sigma_condition_sigma_condition_forall `{Univalence}
    (condf : alg_flab_sigma_condition_forall)
    : alg_flab_sigma_condition S alg_flab_Type_forall.
  Proof.
    intros P PropP A.
    pose (s := (condf _ _ A).1).
    pose (J := (condf _ _ A).2).
    srefine (s; _).
    srefine (pointwise_paths_concat _ J).
    apply ap10. apply path_forall. intros x.
    symmetry; apply (homotopic_alg_flab_map_alg_flab_map_forall P PropP A (s x)).
  Defined.

  Definition sigma_condition_sigma_condition_sigma `{Univalence}
    (condf : alg_flab_sigma_condition_sigma)
    : alg_flab_sigma_condition S alg_flab_Type_sigma.
  Proof.
    intros P PropP A.
    pose (s := (condf _ _ A).1).
    pose (J := (condf _ _ A).2).
    srefine (s; _).
    srefine (pointwise_paths_concat _ J).
    apply ap10. apply path_forall. intros x.
    symmetry; apply (homotopic_alg_flab_map_alg_flab_map_sigma P PropP A (s x)).
  Defined.

End AlgFlabUniverse.

(** The type of pointed types is algebraically flabby. *)
Definition alg_flab_pType `{Univalence}
  : IsAlgebraicFlabbyType {X : Type & X}.
Proof.
  apply (alg_flab_sigma _ alg_flab_Type_forall).
  apply (sigma_condition_sigma_condition_forall _ (@equiv_fun)).
  - intros X. reflexivity.
  - intros P PropP A.
    srefine (idmap; _).
    intros f. apply path_forall. intros h; cbn. reflexivity.
Defined.

(** For a subuniverse, the flabbiness condition is equivalent to closure under proposition indexed pi types (or sigma types), so using this we can state a simpler theorem for proving flabbiness of subuniverses. *)
Definition alg_flab_subuniverse_forall `{Univalence} (O : Subuniverse)
  (condForall : forall P (PropP : IsHProp P) A, (forall h : P, In O (A h)) -> In O (forall h : P, A h))
  : IsAlgebraicFlabbyType@{u su su} (Type_ O).
Proof.
  apply (alg_flab_sigma _ alg_flab_Type_forall).
  apply (sigma_condition_sigma_condition_forall _ (fun X Y f H => @inO_equiv_inO' O X Y H f)).
  - intros X A. apply path_ishprop.
  - intros P PropP A.
    srefine(_; _).
    intros s. apply path_ishprop.
Defined.

Definition alg_flab_subuniverse_sigma `{Univalence} (O : Subuniverse)
  (condSigma : forall P (PropP : IsHProp P) A, (forall h : P, In O (A h)) -> In O {h : P & A h})
  : IsAlgebraicFlabbyType@{u su su} (Type_ O).
Proof.
  apply (alg_flab_sigma _ alg_flab_Type_sigma).
  apply (sigma_condition_sigma_condition_sigma _ (fun X Y f H => @inO_equiv_inO' O X Y H f)).
  - intros X A. apply path_ishprop.
  - intros P PropP A.
    srefine(_; _).
    intros s. apply path_ishprop.
Defined.

(** As an immediate corollary, we get that reflective subuniverses are algebraically flabby. *)
Definition alg_flab_reflective_subuniverse `{Univalence} (O : ReflectiveSubuniverse)
  : IsAlgebraicFlabbyType@{u su su} (Type_ O)
  := alg_flab_subuniverse_forall _ _.
