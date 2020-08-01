Require Import Overture.
Require Import PathGroupoids.

Local Open Scope path_scope.

(** This file contains things that should eventually be put in PathGroupoids.v. *)

(* Not used anywhere. *)
Definition vertical_horizontal {A : Type} {x : A} {p q : x = x} (h : p = 1) (k : 1 = q)
  : h @@ k = (concat_p1 p) @ h @ k @ (concat_1p q)^.
Proof.
  by induction k; revert p h; rapply paths_ind_r.
Defined.

(* Slick proof of Eckmann-Hilton. [horizontal_vertical] is used below, but other things aren't. *)
Definition horizontal_vertical {A : Type} {x : A} {p q : x = x} (h : p = 1) (k : 1 = q)
  : h @ k = (concat_p1 p)^ @ (h @@ k) @ (concat_1p q).
Proof.
  by induction k; revert p h; rapply paths_ind_r.
Defined.

Definition horizontal_vertical' {A : Type} {x : A} {p q : x = x} (h : p = 1) (k : 1 = q)
  : h @ k = (concat_1p p)^ @ (k @@ h) @ (concat_p1 q).
Proof.
  by induction k; revert p h; rapply paths_ind_r.
Defined.

(* The same as [eckmann_hilton]; not used, but can replace existing proof. *)
Definition eckmann_hilton' {A : Type} {x : A} (h k : 1 = 1 :> (x = x)) : h @ k = k @ h
  := (horizontal_vertical h k) @ (horizontal_vertical' k h)^.

Local Open Scope path_scope.
(* This is used below.  Not sure why path_scope is needed here. *)
Definition horizontal_vertical1 {A : Type} {x : A} (h k : 1 = 1 :> (x = x))
  : h @ k = h @@ k
  := horizontal_vertical h k @ concat_p1 _ @ concat_1p _.

Definition horizontal_vertical1' {A : Type} {x : A} (h k : 1 = 1 :> (x = x))
  : h @ k = k @@ h
  := horizontal_vertical' h k @ concat_p1 _ @ concat_1p _.

