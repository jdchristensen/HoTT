Require Import Basics Types.
Require Import Truncations.Core.
Require Import CompactTypes.
Require Import Universes.TruncType Universes.HProp.

(** * We prove that HProp is searchable, assuming univalence. The results should probably be moved to the Universes.HProp and CompactTypes files*)

Definition nn_unit_or_empty_hprop `{Univalence} (P : HProp)
  : ~ ((P <> Unit_hp) * (P <> False_hp)).
Proof.
  intros [h1 h2].
  apply (iff_contradiction (~ P)); constructor.
  - intro p. apply h1. exact (equiv_path_iff_hprop (fun _ => tt, fun _ => p)).
  - intro q. apply h2. exact (equiv_path_iff_hprop (q, Empty_rec)).
Defined.

Definition WeaklyConstant_HProp_to_stable_paths `{Univalence} {A : Type}
  (F : HProp -> A) (s : forall x y : A, Stable (x = y)) (h1 : F Unit_hp = F False_hp)
  : forall (B : HProp), F B = F Unit_hp.
Proof.
  intros B.
  apply (s (F B) (F Unit_hp)); intro h'.
  apply (nn_unit_or_empty_hprop B).
  split; intro p; apply h'.
  - exact (ap F p).
  - exact (ap F p @ h1^).
Defined.

Definition WeaklyConstant_HProp_to_stable_paths' `{Univalence} {A : Type}
  (F : HProp -> A) (s : forall x y : A, Stable (x = y)) (h1 : F Unit_hp = F False_hp)
  : WeaklyConstant F
  := fun B C => WeaklyConstant_HProp_to_stable_paths F s h1 B
                @ (WeaklyConstant_HProp_to_stable_paths F s h1 C)^.

Definition searchable_HProp `{Univalence} : IsSearchable HProp.
Proof.
  intro p.
  remember (p Unit_hp) as b eqn:r; induction b.
  - exact (False_hp; fun h a =>
                       WeaklyConstant_HProp_to_stable_paths p _ (r @ h^) a @ r).
  - exact (Unit_hp; fun h => Empty_rec (true_ne_false (h^ @ r))).
Defined.
