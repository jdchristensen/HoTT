Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import WildCat.

Local Open Scope pointed_scope.

(** Some higher homotopies *)

Definition phomotopy_inverse_1 {A : pType} {P : pFam A} {f : pForall A P}
  : (phomotopy_reflexive f)^* ==* phomotopy_reflexive f.
Proof.
  srapply Build_pHomotopy.
  + reflexivity.
  + pointed_reduce. reflexivity.
Defined.

(** [phomotopy_path] sends concatenation to composition of pointed homotopies.*)
Definition phomotopy_path_pp {A : pType} {P : pFam A}
  {f g h : pForall A P} (p : f = g) (q : g = h)
  : phomotopy_path (p @ q) ==* phomotopy_path p @* phomotopy_path q.
Proof.
  induction p. induction q. symmetry. apply phomotopy_compose_p1.
Defined.

(** [phomotopy_path] respects equality.  *All* functions do, so why have this?? *)
Definition phomotopy_path2 {A : pType} {P : pFam A}
  {f g : pForall A P} {p p' : f = g} (q : p = p')
  : phomotopy_path p ==* phomotopy_path p'.
Proof.
  induction q. reflexivity.
Defined.

(** [phomotopy_path] sends inverses to inverses.*)
Definition phomotopy_path_V {A : pType} {P : pFam A}
  {f g : pForall A P} (p : f = g)
  : phomotopy_path (p^) ==* (phomotopy_path p)^*.
Proof.
  induction p. simpl. symmetry. apply phomotopy_inverse_1.
Defined.

(* TODO: Remove [Funext] when whiskering is reproven without it. *)
Definition phomotopy_hcompose `{Funext} {A : pType} {P : pFam A} {f g h : pForall A P}
 {p p' : f ==* g} {q q' : g ==* h} (r : p ==* p') (s : q ==* q') :
  p @* q ==* p' @* q'.
Proof.
  exact ((s $@R p) $@ (q' $@L r)).
Defined.

Notation "p @@* q" := (phomotopy_hcompose p q).
