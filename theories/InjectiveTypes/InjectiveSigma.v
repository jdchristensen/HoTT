(* -*- mode: coq; mode: visual-line -*- *)
(** * Injectivity for Sigma types and examples of Injective Types which use this setup. *)

(** Many proofs guided by original Agda formalization in the Type Topology Library which can be found at: https://martinescardo.github.io/TypeTopology/InjectiveTypes.Sigma and InjectiveTypes.MathematicalStructuresMoreGeneral. *)

Require Import Basics.
Require Import Types.Forall Types.Sigma Types.Universe.

Require Import InjectiveTypes.
Require Import TypeFamKanExt.


Context {X : Type@{u}} (A : X -> Type@{v}) (Xaf : IsAlgebraicFlabbyType X).

Definition rho_map (P : Type@{w}) (PropP : IsHProp P) (f : P -> X)
  : (A (Xaf _ _ f).1) -> (forall h, A (f h))
  := fun a h => (Xaf _ _ f).2 h # a.

Definition alg_flab_sigma_condition
  : Type@{uvsw}
  := forall P PropP f, {s | (rho_map P PropP f) o s == idmap}.

Definition alg_flab_sigma (cond : alg_flab_sigma_condition)
  : IsAlgebraicFlabbyType {x | A x}.
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
  : IsAlgebraicInjectiveType {x | A x}
  := (alg_inj_alg_flab (alg_flab_sigma cond)).



Context (S : Type@{u} -> Type@{v}).

(*unneccesary?*)
Definition transport_eq `{Univalence} {X Y} (e : X <~> Y) (s : S X)
  : S Y
  := (path_universe_uncurried e) # s.

Section CannonicalMaps.
  Context (P : Type@{u}) (HProp_P : IsHProp P) (A : P -> Type@{u}).

  Local Definition pi_map `{Funext} (h : P)
    : (forall p, A p) <~> (A h).
  Proof.
    transparent assert (C : (Contr P)).
    - srapply contr_inhabited_hprop. apply h.
    - apply (@equiv_contr_forall _ _ C).
  Defined.

  Local Definition phi_map `{Univalence} (h : P)
    : (forall p, A p) = (A h)
    := (path_universe_uncurried (pi_map h)).

  Definition prop_forall_map `{Univalence} (s : S (forall p, A p))
    : forall h, S (A h)
    := fun h => path_universe_uncurried (pi_map h) # s.

End CannonicalMaps.

Definition closed_under_prop_forall `{Univalence}
  : Type@{suv}
  := forall P HProp_P A, IsEquiv (prop_forall_map P HProp_P A).

Definition alg_flabby_sigma_closed_under_prop `{Univalence} (cls : closed_under_prop_forall)
  : IsAlgebraicFlabbyType {X | S X}.
Proof.
  intros P HProp_P f.
  pose (e := Build_Equiv _ _ (prop_forall_map _ _ (pr1 o f)) (cls _ _ (pr1 o f))).
  pose (s := e^-1 (pr2 o f)).
  srefine ((forall p, (f p).1; s); _).
  intros p.
  srapply path_sigma.
  - apply (phi_map _ _ (pr1 o f) p).
  - apply (apD10 (eisretr e (pr2 o f)) p).
Defined.

Definition alg_inj_sigma_closed_under_prop `{Univalence} (cls : closed_under_prop_forall)
  : IsAlgebraicInjectiveType {X | S X}
  := (alg_inj_alg_flab (alg_flabby_sigma_closed_under_prop cls)).
