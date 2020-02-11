Require Import Basics Types Pointed.
Require Import Algebra.Group.
Require Import EquivalenceVarieties.
Require Import Truncations.
Require Import WildCat.
Require Import Cubical.
Require Import PathAny.
Require Import UnivalenceImpliesFunext.
Require Import Tactics.
Import TrM.


(** In this file we develop the theory of magmas or H-magma's to be precise. We show that they live in a "wild category" which can be thought of as the HoTT definition of a category (more precisely a precategory) without the truncation assumption on the homs. This allows us to reuse many lemmas about wild categories such as composition of natural equivalences. *)

(* We use these two idioms several times.  When proving two records are
   equal, we convert to elements of sigma types and use path_sigma to
   reduce to goals involving the components.  Assumes only two components
   in the record, for now. *)
Ltac record_equality :=
  srefine ((equiv_ap' _^-1 _ _)^-1 _); [ | issig | ];
  srapply path_sigma; simpl.

(* Use this one if the fibers are known to be HProps. *)
Ltac record_equality_hprop :=
  srefine ((equiv_ap' _^-1 _ _)^-1 _); [ | issig | ];
  apply path_sigma_hprop; simpl.


(** A [Magma] is a type with an operation. *)
Record Magma := {
  magma_type :> Type;
  magma_op :> SgOp magma_type;
}.

(** We want the operation to be seen by typeclass search. *)
Global Existing Instance magma_op.

(** Here is a helper lemma that shows a magma is equivalent to a sigma type. This allows us to apply lemmas about sigma types to the type of magamas. *)
Definition issig_magma : _ <~> Magma := ltac:(issig).

(** We define a magma map to be an operation preserving map of the underlying types. *)
Record MagmaMap (X Y : Magma) := {
  magmamap_map : X -> Y;
  magmamap_op_preserving : IsSemiGroupPreserving magmamap_map;
}.

Arguments magmamap_map {_ _}.
Arguments magmamap_op_preserving {_ _}.

(** Any magma map can be coerced to the underlying map of types. *)
Coercion magmamap_map : MagmaMap >-> Funclass.

(** We want typeclass search to see such a map is operation preserving. *)
Global Existing Instance magmamap_op_preserving.


(* TODO: Currently, IsGraph is not a parameter of Is01Cat so it clogs up the typeclass search. In the future this will change so we keep these here anyway. *)
(*
(** Magma together with MagmaMap form a graph *)
Global Instance isgraph_magma : IsGraph Magma
  := Build_IsGraph Magma MagmaMap.
*)


(** [MagmaMap] is equivalent to a sigma type. *)
Definition issig_magmamap X Y : _ <~> MagmaMap X Y := ltac:(issig).

(** We can compose magma maps by composing their underlying maps. Typeclass search can then find a semigroup operation preservation from the composition due to it being an instance in Classes.theory.groups. *)
Definition magmamap_compose {X Y Z : Magma}
  (f : MagmaMap Y Z) (g : MagmaMap X Y) : MagmaMap X Z
  := Build_MagmaMap _ _ (f o g) _.

(** The identity magma map. *)
Definition magma_idmap (X : Magma) : MagmaMap X X
  := Build_MagmaMap X X idmap _.

(** This lets us show that Magma is a wild 0-ccategory *)
Global Instance is01cat_magma : Is01Cat Magma.
Proof.
  unshelve nrapply Build_Is01Cat'.
  { apply Build_IsGraph.
    exact MagmaMap. }
  - exact magma_idmap.
  - exact @magmamap_compose.
Defined.

(** Now we define a 2-cell in the category Magma *)
Record Magma2Cell (X Y : Magma) (f g : MagmaMap X Y) := {
  magma2cell_homotopy : f == g;
  magma2cell_op_preserving_homotopy
    : forall x y,
      PathSquare
        (magmamap_op_preserving f x y)
        (magmamap_op_preserving g x y)
        (magma2cell_homotopy (sg_op x y))
        (ap011 sg_op (magma2cell_homotopy x) (magma2cell_homotopy y));
}.

Arguments magma2cell_homotopy {_ _ _ _}.
Arguments magma2cell_op_preserving_homotopy {_ _ _ _}.

Coercion magma2cell_homotopy : Magma2Cell >-> pointwise_paths.

(** TODO: under funext Magma2Cell is equivalent to a path. Or maybe we need more coherence... unless we just truncate. *)

(** Identity magma 2-cell *)
Definition magma2cell_id {X Y : Magma} (f : MagmaMap X Y)
  : Magma2Cell X Y f f.
Proof.
  unshelve rapply Build_Magma2Cell.
  1: reflexivity.
  intros x y.
  apply sq_G1.
  reflexivity.
Defined.

(*
(** 2-cells of magmas turn the 1-cells (magma maps) into graphs *)
Global Instance isgraph_magmamap (X Y : Magma) : IsGraph (MagmaMap X Y)
  := Build_IsGraph (MagmaMap X Y) (Magma2Cell X Y).
*)

(** TODO: move *)
Definition ap011_pp (A B C : Type) (f : A -> B -> C) (x x' x'' : A) (y y' y'' : B)
  (p : x = x') (q : y = y') (p' : x' = x'') (q' : y' = y'')
  : ap011 f (p @ p') (q @ q') = ap011 f p q @ ap011 f p' q'.
Proof.
  by destruct p, p', q, q'.
Defined.

(** TODO: move *)
Definition ap011_V (A B C : Type) (f : A -> B -> C) (x x' : A) (y y' : B)
  (p : x = x') (q : y = y')
  : ap011 f p^ q^ = (ap011 f p q)^.
Proof.
  by destruct p, q.
Defined.

(** We can compose 2-cells of magmas *)
Definition magma2cell_compose {X Y : Magma} (f g h : MagmaMap X Y)
  : Magma2Cell X Y g h -> Magma2Cell X Y f g -> Magma2Cell X Y f h.
Proof.
  intros [p ph] [q qh].
  unshelve rapply Build_Magma2Cell.
  + by transitivity g.
  + intros x y.
    unfold pointwise_paths_concat.
    refine (sq_cccG _^ _).
    1: apply ap011_pp.
    exact (sq_concat_h (qh x y) (ph x y)).
Defined.

(** We can invert 2-cells of magmas *)
Definition magma2cell_inverse {X Y : Magma} (f g : MagmaMap X Y)
  : Magma2Cell X Y f g -> Magma2Cell X Y g f.
Proof.
  intros [p h].
  srapply Build_Magma2Cell.
  1: by symmetry.
  hnf; intros x y.
  refine (sq_cccG _^ _).
  1: apply ap011_V.
  apply sq_flip_h.
  apply h.
Defined.

(** Magma maps form a wild 0-coherent 1-cat *)
Global Instance is01cat_magmamap (X Y : Magma) : Is01Cat (MagmaMap X Y).
Proof.
  unshelve rapply Build_Is01Cat.
  - exact (Magma2Cell X Y).
  - exact magma2cell_id.
  - exact magma2cell_compose.
Defined.

(** TODO: Magma maps form a 0-groupoid (a setoid) *)
Global Instance is0gpd_magmamap (X Y : Magma) : Is0Gpd (X $-> Y).
Proof.
  rapply Build_Is0Gpd.
  exact magma2cell_inverse.
Defined.

Global Instance is0functor_magmamap_precomp (a b c : Magma) (f : MagmaMap a b)
  : Is0Functor (cat_precomp c f).
Proof.
  snrapply Build_Is0Functor.
  intros x y h.
  snrapply Build_Magma2Cell.
  1: intro i; apply h.
  cbn; intros i j.
  refine (sq_concat_v _ _).
  1: apply ap_nat.
  destruct h as [h s].
  apply s.
Defined.

(** TODO: move *)
Definition ap_functor_prod' {A A' B B' : Type} (f : A -> A') (g : B -> B')
  {x x' : A} {y y' : B} (p : x = x') (q : y = y')
  : ap (functor_prod f g) (path_prod' p q) = path_prod' (ap f p) (ap g q).
Proof.
  by destruct p, q.
Defined.

Global Instance is0functor_magmamap_postcomp (a b c : Magma) (f : MagmaMap a b)
  : Is0Functor (cat_postcomp c f).
Proof.
  snrapply Build_Is0Functor.
  intros x y [h s].
  snrapply Build_Magma2Cell.
  1: intro i; cbn; apply ap, h.
  cbn; intros i j.
  refine (sq_concat_v _ _).
  1: apply sq_ap, s.
  refine (sq_ccGG (ap _ _) _ _).
  1,2: apply ap_uncurry.
  refine (sq_ccGG _ _^ _).
  1: exact (ap_compose _ _ (path_prod' (h i) (h j))).
  { refine (ap _ (ap_functor_prod' _ _ _ _)^ @ _).
    refine (ap_compose _ (uncurry sg_op) _)^. }
  pose (magmamap_op_preserving f) as k.
  unfold IsSemiGroupPreserving in k.
  pose (prod_ind (fun x => f (uncurry sg_op x) = uncurry sg_op (functor_prod f f x)) k) as F.
  exact (ap_nat' F (path_prod' (h i) (h j))).
Defined.

(** magma map composition is associative *)
Definition magmamap_compose_assoc {W X Y Z : Magma}
  (h : W $-> X) (g : X $-> Y) (f : Y $-> Z)
  : (f $o g) $o h $== f $o (g $o h).
Proof.
  unshelve rapply Build_Magma2Cell.
  1: reflexivity.
  intros x y.
  apply sq_G1.
  destruct f as [f fp], g as [g gp], h as [h hp].
  cbn; unfold compose_sg_morphism.
  srefine (sq_path^-1 _).
  refine (sq_ccGc _^ _).
  1: apply ap_pp.
  unfold IsSemiGroupPreserving in *.
  refine (sq_concat_h _ _).
  { apply sq_path.
    apply (ap (equiv_concat_r _ _)).
    apply ap_compose. }
  apply sq_path.
  reflexivity.
Defined.

(** Right identity law *)
Definition magmamap_compose_f1 {X Y : Magma} (f : MagmaMap X Y)
  : magmamap_compose f (magma_idmap X) $== f.
Proof.
  unshelve rapply Build_Magma2Cell.
  1: reflexivity.
  intros x y.
  apply sq_G1.
  apply concat_1p.
Defined.

(** Left identity law *)
Definition magmamap_compose_1f {X Y : Magma} (f : MagmaMap X Y)
  : magmamap_compose (magma_idmap Y) f $== f.
Proof.
  unshelve rapply Build_Magma2Cell.
  1: reflexivity.
  intros x y.
  apply sq_G1.
  refine (concat_p1 _ @ _).
  apply ap_idmap.
Defined.

(** Magma is a wild 1-cat *)
Global Instance is1cat_magma : Is1Cat Magma.
Proof.
  nrapply Build_Is1Cat.
  + exact _.
  + exact _.
  + exact @magmamap_compose_assoc.
  + intros a b; apply magmamap_compose_1f.
  + intros a b; apply magmamap_compose_f1.
Defined.

(*
(** Using funext we can show that composition is infact associative. *)
Definition magmamap_compose_assoc (* `{Funext} *) {W X Y Z : Magma}
  (f : MagmaMap Y Z) (g : MagmaMap X Y) (h : MagmaMap W X)
  : magmamap_compose (magmamap_compose f g) h = magmamap_compose f (magmamap_compose g h).
Proof.
  record_equality.
  - reflexivity.
  - funext w0 w1.
    refine (concat_p_pp _ _ _ @ _).
    apply whiskerR.
    refine (_ @ _).
    2: symmetry; apply ap_pp.
    apply whiskerR.
    apply ap_compose.
Defined. *)

Definition path_magmamap_hset `{Funext} {X Y : Magma} {f g : MagmaMap X Y}
  `{IsHSet Y}
  : f == g -> f = g.
Proof.
  intro p.
  record_equality_hprop.
  by apply path_forall.
Defined.

Record MagmaEquiv (X Y : Magma) := Build_MagmaEquiv' {
  magmaequiv_map : MagmaMap X Y;
  magmaequiv_isequiv : IsEquiv magmaequiv_map;
}.

Coercion magmaequiv_map : MagmaEquiv >-> MagmaMap.
Arguments magmaequiv_map {X Y} _.
Arguments magmaequiv_isequiv {X Y} _.
Global Existing Instance magmaequiv_isequiv.

Definition issig_magmaequiv X Y : _ <~> MagmaEquiv X Y := ltac:(issig).

Definition equiv_magmaequiv {X Y : Magma} : MagmaEquiv X Y -> Equiv X Y
  := fun f => Build_Equiv _ _ f _.

Coercion equiv_magmaequiv : MagmaEquiv >-> Equiv.

Definition Build_MagmaEquiv {X Y : Magma}
  (f : X -> Y) (e : IsEquiv f) (r : IsSemiGroupPreserving f)
  : MagmaEquiv X Y
  := (Build_MagmaEquiv' X Y (Build_MagmaMap X Y f r) e).

Definition magmaequiv_eissect (a b : Magma) (f : MagmaMap a b) (fe : IsEquiv f)
  : magmamap_compose (Build_MagmaMap _ _ f^-1 _) f $== magma_idmap a.
Proof.
  srapply Build_Magma2Cell.
  1: exact (eissect f).
  intros x y.
  simpl.
  apply sq_path.
  
  
  unfold compose_sg_morphism.
  unfold id_sg_morphism.
  refine (_ @ (concat_p1 _)^).
  destruct f as [f p].
  cbn in fe.
  simpl.
  
  unfold invert_sg_morphism.
  unfold equiv_inj.
  cbn.
  refine (concat_pp_p _ _ _ @ _).
  apply moveR_Mp.
  apply moveR_pM.
  rewrite ? eisadj, ? eisadj_other.
  rewrite ? ap_V, ? ap_pp.
  rewrite ? inv_pp.
  rewrite ?inv_V.
  rewrite ? concat_pp_p.
  rewrite ?ap_V.
  rewrite ? inv_V.
  rewrite concat_p_pp.
  rewrite concat_Vp.
  rewrite concat_1p.
  rewrite ? concat_p_pp.
(*   rewrite ap_apply_lD2. *)
Admitted.

Definition magmaequiv_eisretr (a b : Magma) (f : MagmaMap a b) (fe : IsEquiv f)
  : magmamap_compose f (Build_MagmaMap _ _ f^-1 _) $== magma_idmap b.
Proof.
  srapply Build_Magma2Cell.
  1: exact (eisretr f).
  intros x y.
  cbn.
Admitted.

(** Thus our wild category Magma has equivalences. *)
Global Instance hasequivs_magma : HasEquivs Magma.
Proof.
  (** To show that the wild cat [Magma] has equivalences we need to give 10 things. *)
  snrapply Build_HasEquivs.
  - (** (1) The Equiv family *)
    exact MagmaEquiv.
  - (** (2) The IsEquiv family *)
    intros a b f.
    exact (IsEquiv f).
  - (** (3) Underlying map of Equiv *)
    intros a b f; exact f.
  - (** (4) IsEquiv of the underlying map of an Equiv *)
    hnf; exact _.
  - (** (5) A way to build Equiv from a map and IsEquiv *)
    exact Build_MagmaEquiv'.
  - (** (6) The underlying map of a built equivalence has a 2-cell to the original map *)
    reflexivity.
  - (** (7) If a map is an equivalence, then it has an inverse map *)
    hnf; intros a b f e.
    rapply (Build_MagmaEquiv f^-1).
  - (** (8) eissect *)
    apply magmaequiv_eissect.
  - (** (9) eisretr *)
    apply magmaequiv_eisretr.
  - (** (10) equiv_adjointify *)
    intros a b f g fg gf.
    apply (isequiv_adjointify f g).
    + apply (magma2cell_homotopy fg).
    + apply (magma2cell_homotopy gf).
Defined.

(** TODO: change names *)
Definition path_magmaequiv `{Funext} {X Y : Magma} (f g : MagmaEquiv X Y)
  : (magmaequiv_map f = magmaequiv_map g) <~> (f = g). 
Proof.
  refine (_^-1 oE _).
  - apply (equiv_ap' (issig_magmaequiv _ _)^-1).
  - refine (equiv_path_sigma_hprop (_;_) (_;_)).
Defined.

(** TODO: redundent *)
Definition magmaequiv_compose {X Y Z : Magma} (g : MagmaEquiv Y Z) (f : MagmaEquiv X Y)
  : MagmaEquiv X Z.
Proof.
  srapply (Build_MagmaEquiv (g oE f)).
  srapply compose_sg_morphism.
Defined.

(* TODO: redundent *)
Definition magmaequiv_inverse {X Y : Magma} (f : MagmaEquiv X Y) : MagmaEquiv Y X.
Proof.
  srapply (Build_MagmaEquiv f^-1).
Defined.

(*
(* The left inverse law.  Much trickier than I expected.  Would be easier with univalence. *)
Definition mecompose_eV `{Funext} {X Y : Magma} (f : MagmaMap X Y) `{!IsEquiv f}
  : f $o f^-1 $== magma_idmap _.
Proof.
  destruct f as [[f r] e].
  record_equality_hprop.
  change (magmamap_map X Y (Build_MagmaMap X Y f r)) with f in *.
  record_equality.
  + apply path_forall; intro; apply eisretr.
  + unfold preserves_sg_op.
    funext y0 y1.
    rewrite transport_forall_constant.
    rewrite transport_forall_constant.
    transport_path_forall_hammer.
    (* The key to making this proof simple was to avoid equiv_inj getting
       unfolded into (ap f)^-1 which would get reduced to a complicated
       expression by simpl/cbn.  We unfold it to (ap f)^-1 now, where it
       cancels against the adjacent (ap f): *)
    unfold compose_sg_morphism, invert_sg_morphism.
    unfold equiv_inj.
    rewrite (eisretr (ap f)).
    rewrite @transport_paths_l.
    do 2 rewrite @transport_paths_Fr.
    rewrite inv_pV.
    do 2 rewrite inv_pp.
    do 6 rewrite concat_pp_p.
    do 3 rewrite concat_V_pp.
    apply concat_Vp.
Defined.


(* Every magma equivalence f has a right inverse f^-1.  So f^-1 has
   both left and right inverses.  It follows that
   (f^-1)^-1 = (f f^-1) (f^-1)^-1 = f (f^-1 (f^-1)^-1) = f. *)
Definition magmaequiv_inverse_inverse `{Funext} {X Y : Magma} (f : MagmaEquiv X Y)
  : magmaequiv_inverse (magmaequiv_inverse f) = f.
Proof.
  apply path_magmaequiv.
  pose (fi := (magmaequiv_inverse f)).
  pose (fii := (magmaequiv_inverse fi)).
  refine (_^ @ _^ @ _ @ _ @ _).
  - exact (magmamap_compose_1f fii).
  - exact (ap (fun k => magmamap_compose (magmamap k) fii) (mecompose_eV f)).
  - apply magmamap_compose_assoc.
  - exact (ap (fun k => magmamap_compose f (magmamap k)) (mecompose_eV fi )).
  - apply magmamap_compose_f1.
Defined.

(* The right inverse law.  Proving this directly requires different
   path algebra than mecompose_eV, so we prove it indirectly. *)
Definition mecompose_Ve `{Funext} {X Y : Magma} (f : MagmaEquiv X Y)
  : magmaequiv_compose (magmaequiv_inverse f) f = magma_idmap _.
Proof.
  refine (_ @ _).
  - exact (ap _ (magmaequiv_inverse_inverse f)^).
  - apply mecompose_eV.
Defined.
*)

Definition issig_magmaequiv' (X Y : Magma) :
  {f : X <~> Y & IsSemiGroupPreserving f} <~> MagmaEquiv X Y.
Proof.
  srapply equiv_adjointify.
  - intros [[f e] r]; exact (Build_MagmaEquiv f e r).
  - intros [[f r] e]; exact ((Build_Equiv _ _ f e); r).
  - simpl. reflexivity.
  - simpl. reflexivity.
Defined.

(** The wild 1-cat [Magma] is univalent... with univalence. *)
Global Instance isunivalent1cat_magma `{Univalence} : IsUnivalent1Cat Magma.
Proof.
  snrapply Build_IsUnivalent1Cat.
  intros X Y.
  snrapply isequiv_homotopic.
  2: srapply equiv_isequiv.
  + refine (issig_magmaequiv' X Y oE _).
    symmetry.
    revert X Y; apply (equiv_path_issig_contr issig_magma); cbn; intros [X m].
    - exists equiv_idmap.  intros x0 x1.  reflexivity.
    - contr_sigsig X (equiv_idmap X).
      exact (@contr_equiv' _ _
        (equiv_functor_sigma_id (fun f => equiv_path_forall11 _ _))^-1
        (contr_basedpaths _)).
  + intros [].
    reflexivity.
Defined.

(** TODO redundant? And also really slow. Really a problem with wild cat. *)
(* This verifies that we have the right notion of equivalence of magmas. *)
Definition equiv_magmaequiv_path `{Univalence} (X Y : Magma)
  : MagmaEquiv X Y <~> (X = Y)
  := Build_Equiv _ _ (cat_path_equiv _ _) _.

(*
(* This also follows directly from Magma Univalence. *)
Definition equiv_magmamap `{Funext} {X Y : Magma} (Z : Magma)
  (e : MagmaEquiv X Y) : MagmaMap Y Z <~> MagmaMap X Z.
Proof.
  srapply equiv_adjointify.
  + exact (fun f => magmamap_compose f e).
  + exact (fun g => magmamap_compose g (magmaequiv_inverse e)).
  + unfold Sect; intro f.
    refine (_ @ _).
    1:apply magmamap_compose_assoc.
    refine ((ap (magmamap_compose f) (ap magmamap (mecompose_Ve e))) @ _).
    apply magmamap_compose_f1.
  + unfold Sect; intro g.
    refine (_ @ _).
    1:apply magmamap_compose_assoc.
    refine ((ap (magmamap_compose g) (ap magmamap (mecompose_eV e))) @ _).
    apply magmamap_compose_f1.
Defined.

Definition equiv_magmamap' `{Funext} {X Y : Magma} (Z : Magma)
  (e : MagmaEquiv X Y) : MagmaMap Z X <~> MagmaMap Z Y.
Proof.
  srapply equiv_adjointify.
  + exact (fun f => magmamap_compose e f).
  + exact (fun g => magmamap_compose (magmaequiv_inverse e) g).
  + unfold Sect; intro f.
    refine (_ @ _).
    1:symmetry; apply magmamap_compose_assoc.
    refine ((ap (fun g => magmamap_compose g f) (ap magmamap (mecompose_eV e))) @ _).
    apply magmamap_compose_1f.
  + unfold Sect; intro g.
    refine (_ @ _).
    1:symmetry; apply magmamap_compose_assoc.
    refine ((ap (fun f => magmamap_compose f g) (ap magmamap (mecompose_Ve e))) @ _).
    apply magmamap_compose_1f.
Defined.
*)

Definition magma_loops (X : pType) : Magma
  := Build_Magma (loops X) concat.

Global Instance is0functor_magma_loops : Is0Functor magma_loops.
Proof.
  srapply Build_Is0Functor.
  intros a b f.
  snrapply Build_MagmaMap.
  + exact (loops_functor f).
  + exact (loops_functor_pp f).
Defined.

(** This is for n.+1 since at n=0 no magma to be found. *)
Definition iterated_magma_loops (n : nat) (X : pType) : Magma
  := Build_Magma (iterated_loops (S n) X) concat.

Global Instance is0functor_iterated_magma_loops (n : nat)
  : Is0Functor (iterated_magma_loops n).
Proof.
  srapply Build_Is0Functor.
  intros a b f.
  snrapply Build_MagmaMap.
  + exact (iterated_loops_functor n.+1 f).
  + exact (iterated_loops_functor_pp f n).
Defined.

Global Instance is1functor_magma_loops : Is1Functor magma_loops.
Proof.
  srapply Build_Is1Functor.
  + intros a b f g p.
    snrapply Build_Magma2Cell.
    - apply (loops_2functor p).
    - intros x y.
      cbn.
      admit.
  + intro a.
    snrapply Build_Magma2Cell.
    - intro.
      refine (concat_1p _ @ concat_p1 _ @ ap_idmap _).
    - admit.
  + intros a b c f g.
    snrapply Build_Magma2Cell.
    1: apply loops_functor_compose.
    admit.
Admitted.

Global Instance is1functor_iterated_magma_loops (n : nat)
  : Is1Functor (iterated_magma_loops n).
Proof.
  snrapply Build_Is1Functor.
  + intros a b f g p.
    snrapply Build_Magma2Cell.
    1: apply iterated_loops_2functor, p.
    admit.
  + intro a.
    snrapply Build_Magma2Cell.
    1: apply iterated_loops_functor_idmap.
    admit.
  + intros a b c f g.
    snrapply Build_Magma2Cell.
    1: apply iterated_loops_functor_compose.
Admitted.

(*
(* It would be nice to replace [==] with [=] here, so that we know the
   magmamap structures agree as well.  That leads to a complicated
   goal, but I would guess that with some pencil-and-paper work first,
   it could be wrangled into something doable. *)
Definition magma_loops_functor_compose {X Y Z : pType} (f : Y ->* Z) (g : X ->* Y)
  : magma_loops_functor (f o* g)
    == magmamap_compose (magma_loops_functor f) (magma_loops_functor g). 
Proof.
  apply loops_functor_compose.
Defined.

Definition iterated_magma_loops_functor {X Y : pType} (n : nat)
  : (X ->* Y) -> MagmaMap (iterated_magma_loops n X) (iterated_magma_loops n Y).
Proof.
Defined.

Definition iterated_magma_loops_functor_compose {X Y Z : pType} (n : nat)
  (f : Y ->* Z) (g : X ->* Y) : iterated_magma_loops_functor n (f o* g)
  == magmamap_compose (iterated_magma_loops_functor n f)
      (iterated_magma_loops_functor n g).
Proof.
  apply iterated_loops_functor_compose.
Defined.

Global Instance isequiv_magma_loops_functor {X Y : pType} (f : X ->* Y)
  : IsEquiv f -> IsEquiv (magma_loops_functor f).
Proof.
  intro e.
  set (g := Build_pEquiv _ _ f e).
  unfold magma_loops_functor.
  unfold magmamap_map.
  exact (pointed_isequiv _ _ (pequiv_loops_functor g)).
Defined.

Global Instance isequiv_iterated_magma_loops_functor {X Y : pType} {n : nat}
  {f : X ->* Y} : IsEquiv f -> IsEquiv (iterated_magma_loops_functor n f).
Proof.
  revert X Y f.
  induction n; exact _.
Defined.

Definition equiv_iterated_magma_loops_functor {X Y : pType} {n : nat}
  {f : X ->* Y} `{!IsEquiv f}
  : MagmaEquiv (iterated_magma_loops n X) (iterated_magma_loops n Y)
  := Build_MagmaEquiv (iterated_magma_loops_functor n f) _ _.
*)



Definition group_to_magma : Group -> Magma
  := fun G => Build_Magma G _.

Coercion group_to_magma : Group >-> Magma.

Definition equiv_grp_homo_magma_map `{F : Funext} (G H : Group)
  : GroupHomomorphism G H <~> MagmaMap G H
  :=  issig_magmamap G H oE (issig_GroupHomomorphism' _ _)^-1.

(** n-connected cover *)
Definition cover (n : trunc_index) (X : pType) : pType
  := @pfiber X (pTr n X) ptr.

Global Instance isconnected_cover (n : trunc_index) (X : pType)
  : IsConnected n (cover n X) := _.

(* The projection map from the n-connected cover to the type. *)
Definition cover_proj (n : trunc_index) {X : pType} : cover n X $-> X.
Proof.
  srapply Build_pMap.
  + apply pr1.
  + reflexivity.
Defined.

Global Instance mapinO_cover_proj (n : trunc_index) {X : pType}
  : IsTruncMap n (@cover_proj (n.+1) X).
Proof.
  srapply mapinO_pr1.
Defined.

(* Lemma 2.3 *)
Global Instance isequiv_postcompose_cover_proj
  (n : trunc_index) (X : pType) (Z : pType) `{IsConnected n Z}
  : IsEquiv (fun f : Z $-> _ => @cover_proj n X $o f).
Proof.
Admitted.

Definition lemma_2_3 (n : nat) (X : pType) (Z : pType) `{IsConnected n Z}
  : (Z $-> cover n X) <~> (Z $-> X)
  := Build_Equiv _ _ _ (isequiv_postcompose_cover_proj n X Z).

(* Truncated magma *)
Definition mTr (n : trunc_index) (X : Magma) : Magma.
Proof.
  srapply (Build_Magma (Tr n X)).
  intros x y.
  strip_truncations.
  exact (tr (sg_op x y)).
Defined.

Definition mtr (n : trunc_index) (X : Magma) : MagmaMap X (mTr n X).
Proof.
  snrapply Build_MagmaMap.
  - exact tr.
  - intros x y. reflexivity.
Defined.

Global Instance isequiv_magmamap_precompose `{Funext} {A B C : Magma}
  (f : MagmaMap A B)
  : IsEquiv f -> IsEquiv (fun g : MagmaMap B C => magmamap_compose g f).
Proof.
  intro e.
  set (fe := Build_MagmaEquiv' _ _ f e).
(*   exact (equiv_isequiv (equiv_magmamap C fe)). *)
Admitted.

Global Instance isequiv_magmamap_postcompose `{Funext} {A B C : Magma}
  (f : MagmaMap B C)
  : IsEquiv f -> IsEquiv (fun g : MagmaMap A B => magmamap_compose f g).
Proof.
  intro e.
  set (fe := Build_MagmaEquiv' _ _ f e).
(*   refine (equiv_isequiv (equiv_magmamap' A fe)). *)
Admitted.

(** BVR 5.1 *)
Global Instance theorem_2_1 (n : nat) (X Y : pType)
  `{IsConnected n X} `{IsConnected n Y} `{IsTrunc n.+1 X} `{IsTrunc n.+1 Y}
  : IsEquiv (fmap (iterated_magma_loops n) (a:=X) (b:=Y)).
Proof.
Admitted.
(* 
Lemma theorem_2_1 (n : nat) (X Y : pType) `{IsConnected n X} `{IsConnected n Y}
  `{IsTrunc n.+1 X} `{IsTrunc n.+1 Y}
  : IsEquiv (@iterated_magma_loops_functor X Y n).
Proof.
Admitted.
 *)

(* Several of the next things should be in Loops.v or pTrunc.v. *)
Global Instance ishset_iterated_magma_loops `{Univalence} (n : nat)
  {X : pType} `{IsTrunc n.+1 X}
  : IsHSet (iterated_magma_loops n X).
Proof.
  unfold iterated_magma_loops.
  unfold magma_type.
  revert X H0.
  induction n.
  - intros X H0.
    apply istrunc_loops.
    exact H0.
  - intros X H0.
    apply (trunc_equiv _ (unfold_iterated_loops' _ _)^-1).
    (* The induction hypothesis and H0 get used automatically by Coq. *)
Defined.

Definition pfiber_loops_functor {A B : pType} (f : A $-> B)
  : loops (pfiber f) $<~> pfiber (loops_functor f).
Proof.
  srapply Build_pEquiv'.
  { symmetry.
    etransitivity.
    2: srapply equiv_path_sigma.
    simpl; unfold hfiber.
    srapply equiv_functor_sigma_id.
    intro p; cbn.
    rewrite transport_paths_Fl.
    refine (_ oE equiv_moveL_Mp _ _ _).
    refine (equiv_moveR_Vp _ _ _ oE _).
    rewrite concat_p1.
    apply equiv_path_inverse. }
  cbn in f.
  by pointed_reduce.
Defined.

Definition pfiber_iterated_loops_functor {A B : pType} (n : nat) (f : A $-> B)
  : iterated_loops n (pfiber f) $<~> pfiber (iterated_loops_functor n f).
Proof.
  induction n.
  1: reflexivity.
  refine (pfiber_loops_functor _ $oE _).
  apply pequiv_loops_functor.
  apply IHn.
Defined.

Global Instance prop_2_5 `{Univalence} (n : nat)
  (X : pType) `{IsConnected n X}
  (Y : pType) `{IsTrunc n.+1 Y}
  : IsEquiv (fmap (iterated_magma_loops n) (a:=X) (b:=Y)).
Proof.
  (** We prove this is an equivalence by constructing a commutative square of equivalences *)
  snrapply isequiv_commsq.
  (** Bottom left corner *)
  1: exact (pTr n.+1 X $-> Y).
  (** Bottom right corner *)
  1: exact (MagmaMap (iterated_magma_loops n (pTr n.+1 X))
    (iterated_magma_loops n Y)).
  (** Bottom horizontal map *)
  1: exact (fmap (iterated_magma_loops n)).
  (** Left vertical map is [fun f => f o* ptr], but we hint that it's an equivalence: *)
  { apply equiv_fun.
    apply equiv_ptr_rec. }
  (** Right vertical map *)
  { intro g.
    refine (_ $o fmap (iterated_magma_loops _) _).
    1: apply g.
    apply ptr. }
  (** The square commutes by functoriality of iterated_magma_loops *)
  { symmetry.
    intro f.
    (* Make typeclass resolution faster in next line. *)
    pose (HS := ishset_iterated_magma_loops n (X:=Y)).
    rapply path_magmamap_hset.
    refine (fmap_comp (iterated_magma_loops _) _ _). }
  (** Immediately we have some equivalences. *)
  2: exact _.
  2: {
  apply isequiv_magmamap_precompose.
(*     apply isequiv_iterated_magma_loops_functor. *)
    (* TODO: but tr is not an equivalence? *)
    admit. }
  (** To prove this final map is an equivalence we use another commutative square. *)
  snrapply isequiv_commsq.
  (** The bottom left type *)
  1: exact (pTr n.+1 X $-> cover n Y).
  (** The bottom right type *)
  1: exact (MagmaMap (iterated_magma_loops n (pTr n.+1 X))
    (iterated_magma_loops n (cover n Y))).
  (** The bottom map *)
  1: exact (fmap (iterated_magma_loops n)).
  (** The left map *)
  { apply equiv_fun.
    apply lemma_2_3.
    exact _. }
  (** The right map *)
  { intro g.
    refine (fmap (iterated_magma_loops n) _ $o g).
    apply cover_proj. }
  (** The square commutes by functoriality of iterated_magma_loops *)
  { cbn.
    symmetry.
    intro f.
    apply path_magmamap_hset.
    refine (fmap_comp (iterated_magma_loops n) _ _). }
  (** The left map is an equivalence *)
  2: exact _.
  2: { apply isequiv_magmamap_postcompose.
    (** Argument by using UP of connected types and loop-space sphere stuff *)
    admit. }
  srapply theorem_2_1.
Admitted.

Definition magma_loops_pmap (Y Z : pType) : Magma.
Proof.
  srapply (Build_Magma (pMap Y (Build_pType (magma_loops Z) idpath))).
  intros f g.
  srapply Build_pMap.
  { intro y.
    exact (sg_op (f y) (g y)). }
  simpl; by rewrite 2 point_eq.
Defined.

Definition pmap_const {X Y : pType} : X $-> Y
  := Build_pMap X Y (fun _ => point _) idpath.

Definition ispointed_pmap {X Y : pType} : IsPointed (X $-> Y)
  := pmap_const.

Notation "X ->** Y" := (Build_pType (X $-> Y) ispointed_pmap) (at level 15).

Definition ap_const' {A B : Type} {x y : A} (p : x = y) (f : A -> B) {b : B}
  (q : forall a, f a = b) : ap f p = q x @ (q y)^.
Proof.
  destruct p.
  symmetry.
  apply concat_pV.
Defined.

Definition foo `{Funext} {Y Z : pType}
  : MagmaMap (magma_loops (Y ->** Z)) (magma_loops_pmap Y Z).
Proof.
  snrapply Build_MagmaMap.
  + change (loops (Y ->** Z) -> magma_loops_pmap Y Z).
    change (loops (Y ->** Z) -> (Y $-> loops Z)).
    intro p.
    srapply Build_pMap.
    { intro y.
      exact (ap (fun f : Y $-> Z => pointed_fun f y) p). }
    srapply (ap_const' p _ point_eq).
  + intros p q.
    srapply path_pmap.
    srapply Build_pHomotopy.
    { intro x; cbn.
      exact (ap_pp _ p q). }
Admitted.



