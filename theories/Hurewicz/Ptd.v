Require Import Basics Pointed.

Local Open Scope pointed_scope.

(** This file contains things that should eventually be put somewhere in the Pointed directory. *)

(** Pointed composition maps. *)

(* Precomposing with the constant map gives the constant map. *)
Lemma precompose_pconst_as_path {A B C : pType} (f : B ->* C)
  : f o* @pconst A B = pconst.
Proof.
  pointed_reduce_pmap f; reflexivity.
(* Or:
  record_equality.
  - apply (ap (fun c => (fun _ => c)) (point_eq f)).
  - cbn.
    rewrite transport_paths_Fl.
    cbn.
    rewrite <- (ap_compose (fun c => (fun _ => c))).
    rewrite ap_idmap.
    rewrite concat_1p.
    apply concat_Vp.
*)
Defined.

Definition ppostcompose (A : pType) {B C : pType} (f : B ->* C) :
  (A ->** B) ->* (A ->** C).
Proof.
  simple refine (Build_pMap _ _ _ _).
  - exact (fun g => f o* g).
  - apply precompose_pconst_as_path.
Defined.

(* Postcomposing with the constant map gives the constant map. *)
Lemma postcompose_pconst_as_path {A B C : pType} (f : A ->* B)
  : pconst o* f = @pconst A C.
Proof.
  pointed_reduce_pmap f; reflexivity.
(* Or:
  record_equality.
  - reflexivity.
  - cbn.
    exact (concat_p1 _ @ ap_const _ _).
*)
Defined.

Definition pprecompose {A B : pType} (C : pType) (f : A ->* B) :
  (B ->** C) ->* (A ->** C).
Proof.
  simple refine (Build_pMap _ _ _ _).
  - exact (fun g => g o* f).
  - apply postcompose_pconst_as_path.
Defined.

Definition pcompose `{Funext} {A B C : pType} : (B ->** C) ->* ((A ->** B) ->** (A ->** C)).
Proof.
  snrapply Build_pMap.
  1: apply ppostcompose.
  apply path_pforall.
  snrapply Build_pHomotopy.
  - intro g.
    cbn.  unfold "o*".  cbn.
    (* The functions are definitionally equal, so we reduce to comparing the proofs of pointedness. *)
    refine (ap (fun H => Build_pMap A C (fun _ : A => point C) H) _).
    refine (concat_p1 _ @ _).
    rapply ap_const.
  - cbn.  reflexivity.
Defined.

Definition nested_pcompose `{Funext} {A A' B : pType} (C : pType)
  : (B ->** C) ->* ((A ->** (A' ->** B)) ->** (A ->** (A' ->** C)))
  := pcompose o* pcompose.

Definition peval {A B C : pType} (b : B) : (A ->** (B ->** C)) ->* (A ->** C).
Proof.
  snrapply Build_pMap.
  - intro f.
    snrapply Build_pMap.
    + exact (fun a => f a b).
    + simpl.
      exact (ap (fun g : B ->* C => g b) (point_eq f)).
  - reflexivity.
Defined.

Definition nested_pprecompose `{Funext} {A A' B : pType} (C : pType) (f : (A ->** (A' ->** B)))
  : (B ->** C) ->* (A ->** (A' ->** C))
  := peval f (nested_pcompose C).

Definition phomotopy_inv2 `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
           {p q : f ==* g} (r : p ==* q)
  : p^* ==* q^*.
Proof.
  pointed_reduce.
  snrapply Build_pHomotopy.
  - intro a; cbn.
    apply (ap _ (r a)).
  - cbn.
    (* [induction (r point)] works here to simplify things. *)
    unfold inverse2.
    symmetry.
    refine (((ap_pp _ _ _) @@ 1) @@ (inv_pp _ _) @ _).
    refine (concat_pp_p _ _ _ @ _).
    refine (1 @@ concat_p_Vp _ _ @ _).
    apply concat_pp_V.
Defined.

(** Things about [phomotopy_path]. *)

(** [phomotopy_path] sends concatenation to composition of pointed homotopies.*)
(** TODO: move to pHomotopy.v. *)
Definition phomotopy_path_pp_aspath {A : pType} {P : pFam A}
  {f g h : pForall A P} (p : f = g) (q : g = h)
  : phomotopy_path (p @ q) = phomotopy_path p @* phomotopy_path q.
Proof.
  pointed_reduce.  reflexivity.
Defined.

(** TODO: move to Pointed/Core.v. *)
Global Instance isequiv_phomotopy_path `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
  : IsEquiv (@phomotopy_path A P f g).
Proof.
  rapply (transport IsEquiv).
  - symmetry; rapply path_equiv_path_pforall_phomotopy_path.
  - exact _.
Defined.

Definition phomotopy_path_pconst {Y Y' Z : pType} (f : Y ->* Y')
  : phomotopy_path (postcompose_pconst_as_path f) ==* postcompose_pconst (C:=Z) f.
Proof.
  (* Manually applying [pointed_reduce_pmap], since the last [cbn] is slow. *)
  destruct Y' as [Y' y0'], f as [f ptd].
  cbn in f, ptd; destruct ptd.
  reflexivity.
Defined.

(* TODO: Generalize to dependent functions? *)
(* TODO: Move to somewhere in Pointed directory. *)
Definition phomotopy_path_nat_l {Y Y' Z : pType} (h h' : Y' ->* Z) (f : Y ->* Y') (p : h = h')
  : phomotopy_path (ap (pprecompose Z f) p)
    = (pmap_prewhisker f) (phomotopy_path p).
Proof.
  pointed_reduce; reflexivity.
Defined.

(* TODO: Generalize to dependent functions? *)
Definition phomotopy_path_nat_r {Y Z Z' : pType} (h h' : Y ->* Z) (f : Z ->* Z') (p : h = h')
  : phomotopy_path (ap (fun g => f o* g) p)
    = (pmap_postwhisker f) (phomotopy_path p).
Proof.
  pointed_reduce; reflexivity.
Defined.
