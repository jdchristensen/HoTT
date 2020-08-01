Require Import Coq.Init.Peano.
Require Import Spaces.Nat.
Require Import Basics Types Pointed.
Require Import Hurewicz.PathGpd.  (* Temporary. *)
Require Import ReflectiveSubuniverse.
Require Import Truncations.
Require Import Algebra.AbGroups.
Require Import HomotopyGroup.
Require Import Hurewicz.HomotopyGroup2.
Require Import Hurewicz.PreGroup.
Require Import HoTT.Tactics.

Local Open Scope pointed_scope.

(* TODO: move to Loops.v *)
Lemma iterated_loops_sum (n m : nat) (X : pType)
  : iterated_loops (n+m) X = iterated_loops n (iterated_loops m X).
Proof.
  induction n.
  1: reflexivity.
  cbn.
  exact (ap loops IHn).
Defined.

Lemma equiv_iterated_loops_sum (n m : nat) (X : pType)
  : iterated_loops (n+m) X <~>* iterated_loops n (iterated_loops m X).
Proof.
  induction n.
  1: reflexivity.
  cbn.
  exact (pequiv_loops_functor IHn).
(* Or:
  apply pequiv_path.
  apply iterated_loops_sum.
*)
Defined.

Lemma equiv_iterated_loops_sum' (n m : nat) (X : pType)
  : iterated_loops (n+m) X <~>* iterated_loops m (iterated_loops n X).
Proof.
  transitivity (iterated_loops (m+n) X).
  - apply pequiv_path.
    apply (ap (fun k => iterated_loops k X) (nat_plus_comm n m)).
  - apply equiv_iterated_loops_sum.
Defined.

(* TODO: move to Groups?  Use ->Grp? *)
Notation "X '->G' Y" := (GroupHomomorphism X Y) (at level 15, right associativity).

Local Open Scope mc_add_scope.

(* TODO: generalize the version in AbelianGroup.v.  The only change is in the type of A. *)
(** Homomorphisms from a group to an abelian group form an abelian group. *)
Definition AbHom' (A : Group) (B : AbGroup) `{Funext} : AbGroup.
Proof.
  snrapply (Build_AbGroup (GroupHomomorphism A B)).
  + intros f g.
    snrapply Build_GroupHomomorphism.
    - intro x; exact (f x + g x).
    - intros x y.
      rewrite 2 grp_homo_op.
      rewrite 2 simple_associativity.
      rewrite <- (simple_associativity (f _) (g _)).
      rewrite (commutativity (g _) (f _)).
      rewrite simple_associativity.
      reflexivity.
  + snrapply Build_GroupHomomorphism.
    - intro; exact mon_unit.
    - intros x y.
      symmetry.
      apply left_identity.
  + intro f.
    snrapply Build_GroupHomomorphism.
    - intro x; exact (- f x).
    - intros x y.
      rewrite grp_homo_op.
      apply negate_sg_op_distr.
  + repeat split.
    1: exact _.
    all: hnf; intros; apply equiv_path_grouphomomorphism; intro; cbn.
    - apply associativity.
    - apply left_identity.
    - apply right_identity.
    - apply left_inverse.
    - apply right_inverse.
    - apply commutativity.
Defined.

Local Close Scope mc_add_scope.

Notation "X '->A' Y" := (AbHom' X Y) (at level 15, right associativity).

Definition magma_trunc (n : nat) (A : Magma) : Magma.
Proof.
  srapply (Build_Magma (Trunc n A)).
  intros a b.
  strip_truncations.
  exact (tr (sg_op a b)).
Defined.

(* Not needed, but seems handy. *)
Definition magmamap_to_trunc (n : nat) (A : Magma) : MagmaMap A (magma_trunc n A).
Proof.
  snrapply Build_MagmaMap.
  1: exact tr.
  apply tr.
  intros a b.
  reflexivity.
Defined.  

(* It might be easier to define the map in the other direction and show that it is an equivalence. *)
Definition magmamap_trunc_rec {A B : Magma} (n : nat) `{IsTrunc n B}
  : MagmaMap A B -> MagmaMap (magma_trunc n A) B.
Proof.
  intro f.
  snrapply Build_MagmaMap.
  1: exact (Trunc_rec f).
  pose proof (magmamap_op_preserving f) as r.
  strip_truncations.
  apply tr.
  (* Manually apply [strip_truncations], to make it faster: *)
  intro a0. rapply Trunc_ind; intro a1.
  revert a0; rapply Trunc_ind; intro a0.
  cbn.
  apply r.
Defined.

(* Not needed, but seems handy. *)
Definition magmamap_trunc_functor {A B : Magma} (n : nat)
  : MagmaMap A B -> MagmaMap (magma_trunc n A) (magma_trunc n B).
Proof.
  intro f.
  rapply magmamap_trunc_rec.
  exact (magmamap_compose (magmamap_to_trunc n B) f).
Defined.

(* [eckmann_hilton] applies to [loops (loops Z)]. Adapt it to the case where there is at least one inner loop and one outer loop. *)
(* TODO: move to Loops.v? *)
Definition iterated_eckmann_hilton {A : pType} (m : nat) (p q : iterated_loops m.+1 (loops A))
  : p @ q = q @ p.
Proof.
  induction m; apply eckmann_hilton.
Defined.

(* Let's focus on the inner part of the smashing map. *)

(* It will be useful to isolate the concept of a pointed magma structure on a pointed type. *)
(* TODO: In the end, I'm not sure this ends up being needed, or if we need any of the "inner" structures. *)
Definition pMagmaStructure (X : pType) := { mu : SgOp X & mu (point X) (point X) = point X }.

Definition Build_pMagma' (X : pType) (mu : pMagmaStructure X) : pMagma
  := Build_pMagma (Build_Magma X mu.1) (point X) mu.2.

Definition pmagma_structure (X : pMagma) : pMagmaStructure X
  := (magma_op (pmagma_magma X); pmagma_idem X).

(* Every loop space has a pmagma structure. *)
Definition pmagma_structure_loops (X : pType) : pMagmaStructure (loops X)
  := pmagma_structure (pmagma_loops X).

(* The loop space of a pointed magma gets an induced pointed magma structure from the original magma structure. *)
Definition loops_pmagma_structure {X : pType} (mu : pMagmaStructure X): pMagmaStructure (loops X).
Proof.
  snrefine (_; _).
  - intros p q.
    exact (mu.2^ @ (ap011 mu.1 p q) @ mu.2).
    (*exact ((pmagma_idem X)^ @ (ap011 sg_op p q) @ (pmagma_idem X)).*)
  - cbn.
    exact ((whiskerR (concat_p1 _) _) @ (concat_Vp _)).
Defined.

Definition loops_pmagma (X : pMagma) : pMagma
  := Build_pMagma' (loops X) (loops_pmagma_structure (pmagma_structure X)).

(** When [Y] is a loop space, the two magma structures on [loops Y] agree. (This is also true when [Y] is an H-space with the condition that the two proofs that [y0 * y0 = y0] are equal. *)
Definition interchange_loops_loops `{Funext} (X : pType)
 (p q : magma_loops (loops X))
  : sg_op p q = @sg_op (loops_pmagma (pmagma_loops X)) _ p q.
Proof.
  cbn.
  snrapply horizontal_vertical.
Defined.

(** In fact, the two pointed magma structures on [loops (loops X)] agree. Could talk about pmagma structures being "homotopic" and avoid Funext, but for now we'll use Funext. *)
Definition pmagma_structure_double_loops `{Funext} (X : pType)
  : pmagma_structure_loops (loops X) = loops_pmagma_structure (pmagma_structure_loops X).
Proof.
  snrapply path_sigma.
  - cbn.
    funext p q.
    apply interchange_loops_loops.
  - cbn.
    (* [transport_path_forall_hammer] works, but we can avoid the rewrites pretty easily. *)
    transport_path_forall_hammer_helper.
    refine (_ @ _); [snrapply transport_const | ].
    transport_path_forall_hammer_helper.
    snrapply transport_const.
Defined.

(** Iterated versions of the above. *)

(** First the pointed magma structure coming from the outermost loop space.  Note that we don't use the induction hypothesis, and only use that X is a pointed magma in the case where [n] is [0]. *)
Definition pmagma_structure_outer_iterated_loops (n : nat) {X : pType} (mu : pMagmaStructure X)
  : pMagmaStructure (iterated_loops n X).
Proof.
  induction n.
  - exact mu.
  - exact (pmagma_structure_loops (iterated_loops n X)).
Defined.

Definition pmagma_outer_iterated_loops (n : nat) (X : pMagma) : pMagma
  := Build_pMagma' (iterated_loops n X) (pmagma_structure_outer_iterated_loops n (pmagma_structure X)).

(** Now the version where the inner magma structure is used to induce the magma structure on the iterated loop space. If you iterate [loops_pmagma] in the obvious way, then its underlying type isn't definitionally [iterated_loops n X], so we instead fix the underlying type, and produce the pointed magma structure by induction. *)
Definition pmagma_structure_inner_iterated_loops (n : nat) {X : pType} (mu : pMagmaStructure X)
  : pMagmaStructure (iterated_loops n X).
Proof.
  induction n.
  - exact mu.
  - snrapply (loops_pmagma_structure IHn).
Defined.

Definition pmagma_inner_iterated_loops (n : nat) (X : pMagma) : pMagma
  := Build_pMagma' (iterated_loops n X) (pmagma_structure_inner_iterated_loops n (pmagma_structure X)).

(** This is the general form of Eckmann-Hilton.  By taking [X] to be an iterated loop space, this says that in a [k]-fold iterated loop space, all [k] operations agree. It could be strengthened to say that they agree as H-space structures. *)
Definition pmagma_structure_iterated_loops `{Funext} (n : nat) (X : pType)
  : pmagma_structure_outer_iterated_loops n (pmagma_structure_loops X)
  = pmagma_structure_inner_iterated_loops n (pmagma_structure_loops X).
Proof.
  induction n.
  - cbn.  reflexivity.
  - simpl.
    refine (_ @ ap loops_pmagma_structure IHn).
    induction n; srapply pmagma_structure_double_loops.
Defined.

(** The last result can be rephrased as saying that the identity map is a pmagma equivalence.  This is true in a strong sense, but we state it for our weak sense. *)
Definition pmagma_iterated_loops `{Funext} (n : nat) (X : pType)
  : pMagmaEquiv (pmagma_outer_iterated_loops n (pmagma_loops X))
                (pmagma_inner_iterated_loops n (pmagma_loops X)).
Proof.
  snrapply Build_pMagmaEquiv.
  - snrapply Build_pMagmaMap.
    + snrapply Build_MagmaMap.
      * exact idmap.
      * apply tr.  unfold IsSemiGroupPreserving.
        intros x y.
        apply ap10; apply ap10.
        unfold sg_op.  cbn.
        apply (ap pr1).
        srapply pmagma_structure_iterated_loops.
    + cbn.  reflexivity.
  - exact _.
Defined.

(* The pointed magma of pointed magma maps from a pointed magma to a commutative, associate pointed magma. *)
Definition pmagma_pmagmamap (Y Z : pMagma)
           (C : merely (Commutative (magma_op Z)))
           (A : merely (Associative (magma_op Z)))
           : pMagma.
Proof.
  snrapply Build_pMagma.
  - snrapply (Build_Magma (pMagmaMap Y Z)).
    intros f g.
    snrapply (Build_pMagmaMap _ _ (Build_MagmaMap _ _ _ _) _).
    + intro y; exact (sg_op (f y) (g y)).
    + pose proof (magmamap_op_preserving f) as r.
      pose proof (magmamap_op_preserving g) as s.
      strip_truncations.
      apply tr.
      intros y y'.
      refine (ap011 sg_op _ _ @ _); [apply r | apply s |].
      unfold Associative in A.  unfold HeteroAssociative in A.
      refine ((A _ _ _)^ @ _ @ A _ _ _).
      refine (ap (fun p => sg_op (f y) p) _).
      refine (A _ _ _ @ _ @ (A _ _ _)^).
      refine (ap (fun p => sg_op p (g y')) _).
      apply C.
    + cbn.  unfold ispointed_loops.
      exact ((ap011 sg_op (point_eq f) (point_eq g)) @ pmagma_idem Z).
  - cbn.
    snrapply (Build_pMagmaMap _ _ (Build_MagmaMap _ _ _ _) _).
    + exact (fun _ => (pmagma_pointed Z)).
    + apply tr.
      intros y1 y2.
      exact (pmagma_idem Z)^.
    + cbn.
      reflexivity.
  - apply path_pmagmamap.
    unfold pmap_pmagmamap.
    cbn.
    record_equality.
    + exact (ap (fun z => fun _ : Y => z) (pmagma_idem Z)).
    + refine (transport_paths_Fl _ _ @ _).
      apply moveR_Vp.
      refine (concat_1p _ @ _ @ (concat_p1 _)^).
      refine (_ @ ap_compose (fun z => (fun _ : Y => z)) _ _).
      symmetry.
      apply ap_idmap.
Defined.

(** The pointed magma of all pointed magma maps from a pointed magma to an (m+2)-fold loop space. *)
Definition pmagma_pmagmamap_loops (m : nat) (Y : pMagma) (Z : pType) : pMagma.
Proof.
  (* The codomain is the (m+2)-fold loop space, with one loop on the inside and one on the outside. *)
  snrapply (pmagma_pmagmamap Y (iterated_pmagma_loops m (loops Z))).
  - apply tr.
    rapply iterated_eckmann_hilton.
  - apply tr.
    rapply concat_p_pp.
Defined.

Definition ap_pointwise_product {Y : Type} {Z : pMagma} (f g : Y -> Z) {y1 y2 : Y} (p : y1 = y2)
  : ap (fun y => sg_op (f y) (g y)) p = ap011 sg_op (ap f p) (ap g p)
  := match p with idpath => idpath end.

Definition ap011_VV {A B C} (f : A -> B -> C) {x x' y y'} (p : x = x') (q : y = y')
  : ap011 f p^ q^ = (ap011 f p q)^
  := match p, q with idpath, idpath => idpath end.

Definition ap011_pp {A B C} (f : A -> B -> C) {x1 x2 x3 y1 y2 y3} (p1 : x1 = x2) (p2 : x2 = x3)
           (q1 : y1 = y2) (q2 : y2 = y3)
  : ap011 f (p1 @ p2) (q1 @ q2) = (ap011 f p1 q1) @ (ap011 f p2 q2).
Proof.
  by destruct p1, p2, q1, q2.
Defined.

Local Definition magmamap_loops_functor_helper {Z : pType} (a b : loops Z) (p : a = 1) (q : b = 1)
  : (inv_pp (ap011 concat p q) 1 @@ (1 @@ concat_p1 (ap011 concat p q))) @
    ((concat_1p (ap011 concat p q)^ @@ 1) @
     (((horizontal_vertical1 (p^ @ (1 @ p)) (q^ @ (1 @ q)) @
        ap011_pp concat p^ (1 @ p) q^ (1 @ q)) @ (1 @@ ap011_pp concat 1 p 1 q)) @
      (ap011_VV sg_op p q @@ 1))^) =
    ((1 @@ concat_1p (ap011 sg_op p q @ 1)) @ concat_Vp (ap011 sg_op p q @ 1)) @
    (ap011 concat ((1 @@ concat_1p p) @ concat_Vp p) ((1 @@ concat_1p q) @ concat_Vp q) @ 1)^.
Proof.
  revert a p; rapply paths_ind_r.
  revert b q; by rapply paths_ind_r.
Defined.

Definition pmagma_loops_functor {Y Z : pType} (f : Y ->* Z)
  : pMagmaMap (pmagma_loops Y) (pmagma_loops Z).
Proof.
  snrapply Build_pMagmaMap.
  + exact (magma_loops_functor f).
  + cbn.  exact ((1 @@ concat_1p _) @ concat_Vp _).
Defined.

(** The map [loops_functor] from [Y ->* loops Z] to [loops Y ->M,* loops (loops Z)] is a magma map. *)
Definition magmamap_loops_functor `{Funext} {Y Z : pType}
  : MagmaMap (pmagma_pmap Y (pmagma_loops Z)) (pmagma_pmagmamap_loops 0 (pmagma_loops Y) Z).
Proof.
  snrapply Build_MagmaMap.
  - apply pmagma_loops_functor.
  - apply tr.
    intros f g.
    apply path_pmagmamap.  unfold pmap_pmagmamap; simpl.
    apply path_pforall.
    snrapply Build_pHomotopy.
    + cbn.
      intro p.
      unfold sg_op.
      refine (inv_pp _ _ @@ ((ap_pointwise_product (Z:=pmagma_loops Z) _ _ _) @@ (concat_p1 _)) @ _).
      refine (concat_1p _ @@ 1 @ _).
      symmetry.
      refine (_ @ (ap011_VV _ _ _ @@ 1)).
      refine (_ @ (1 @@ ap011_pp concat (ap f p) (point_eq f) (ap g p) (point_eq g))).
      refine (_ @ ap011_pp concat _ _ _ _).
      snrapply horizontal_vertical1.
    + snrapply magmamap_loops_functor_helper.
      (* The type of helper was found using:
        unfold Build_pMap, dpoint_eq.
        change (point (ptype_pmagma (pmagma_loops Y))) with (@idpath Y (point Y)).
        unfold ap, ap_pointwise_product.
        destruct f as [f p]. cbn in p.
        destruct g as [g q]; cbn in q.
        unfold point_eq, dpoint_eq.
      *)
Defined. (* A bit slow. *)

(* The forgetful map [pmap_pmagmamap] from pointed magma maps to magma maps is a pointed magma map. *)
Definition pmagmamap_pmap_pmagmamap {Y : pMagma} {Z : pType} (m : nat)
  : pMagmaMap (pmagma_pmagmamap_loops m Y Z)
             (pmagma_pmap Y (iterated_pmagma_loops m (loops Z))).
Proof.
  snrapply Build_pMagmaMap.
  1: snrapply Build_MagmaMap.
  - exact pmap_pmagmamap.
  - apply tr; intros f g.
    reflexivity.
  - reflexivity.
Defined.

Definition magmamap_iterated_loops_functor `{Funext} {Y Z : pType} (m : nat)
  : MagmaMap (pmagma_pmap Y (pmagma_loops Z))
             (pmagma_pmagmamap_loops m (pmagma_loops (iterated_loops m Y)) Z).
Proof.
  induction m.
  - exact magmamap_loops_functor.
  - refine (magmamap_compose _ IHm).
    refine (magmamap_compose _ (pmagmamap_pmap_pmagmamap m)).
    exact magmamap_loops_functor.
Defined.

Definition pi_functor_magmamap {Y Z : pType} (f : MagmaMap (pmagma_loops Y) (pmagma_loops Z))
  : Pi 1 Y ->G Pi 1 Z.
Proof.
  snrapply Build_GroupHomomorphism.
  - exact  (Trunc_functor 0 f).
  - intros a b.
    pose proof (magmamap_op_preserving f) as r.
    (* The next two [pose] commands speed up [strip_truncations] a bit. *)
    pose istrunc_truncation; pose istrunc_paths.
    strip_truncations.
    (* For some reason it's tricky to get this to simplify nicely. *)
    change (@tr 0 _ (f (a @ b)) = tr (f a @ f b)).
    exact (ap tr (r a b)).
Defined.

(* This is the case where m = n = 0, but it also handles the general case. *)
Definition magmamap_pi_functor `{Funext} {Y Z : pType}
  : MagmaMap (pmagma_pmagmamap_loops 0 (pmagma_loops Y) Z)
             (Pi 1 Y ->A Pi' 2 Z).
Proof.
  snrapply Build_MagmaMap.
  - exact pi_functor_magmamap.
  - apply tr.
    intros f g.
    apply equiv_path_grouphomomorphism.
    (* The next two [pose] commands speed up [Trunc_ind] a bit. *)
    pose istrunc_truncation; pose istrunc_paths.
    rapply Trunc_ind.
    intro a.
    reflexivity.
Defined.

Definition pmagma_loops_shuffle (m n : nat) (Z : pType)
  : iterated_pmagma_loops 0 (pmagma_loops (iterated_loops (m + n) Z)) =
    iterated_pmagma_loops m (pmagma_loops (iterated_loops      n  Z)).
Proof.
  unfold iterated_pmagma_loops.
  refine (ap pmagma_loops _).
  change (iterated_loops (m + n).+1 Z = iterated_loops m (iterated_loops n.+1 Z)).
  refine (_ @ iterated_loops_sum m n.+1 Z).
  refine (ap (fun k => iterated_loops k Z) _).
  apply nat_plus_n_Sm.
Defined.

(** Name?? *)
Definition ap0111D {A : Type} {B : A -> Type} {C : A -> Type} {D : Type} (f : forall a, B a -> C a -> D)
           (a a' : A) (b : B a) (b' : B a') (c : C a) (c' : C a')
           (p : a = a') (q : transport B p b = b') (r : transport C p c = c')
  : f a b c = f a' b' c'.
Proof.
  induction p.  cbn in *.
  induction q, r.  reflexivity.
Defined.

Definition pmagma_pmagmamap_shuffle `{Funext} (m n : nat) (Y : pMagma) (Z : pType)
  : pmagma_pmagmamap_loops 0 Y (iterated_loops (m + n) Z) =
    pmagma_pmagmamap_loops m Y (iterated_loops n Z).
Proof.
  unfold pmagma_pmagmamap_loops.
  srapply (ap0111D (pmagma_pmagmamap Y) _ _ _ _ _ _ (pmagma_loops_shuffle m n Z)).
  1,2: apply path_ishprop.
Defined.

(* This is the inner magma map in Equation 2.1 of CS, going from the RHS of the first line to the fifth line. *)
Definition smashing_inner `{Funext} (Y Z : pType) (n m : nat)
  : MagmaMap (iterated_pmagma_loops n (Y ->** Z))
             (Pi m.+1 Y ->A Pi' (m.+2 + n) Z).
Proof.
  (* Once we have set up the right wild categories, we will be able to express this simply as a [$o] composite of various magma maps, and even of natural transformations. That will require adjustments to the "shuffle" part. *)
  (* Specifying [Z] here makes the next goal easier to understand: *)
  rapply (magmamap_compose (magmamap_pi_functor (Z:=iterated_loops (m+n) Z))).
  (* Target is now the fourth line of (2.1). *)
  rewrite pmagma_pmagmamap_shuffle.
  (* Target is now the third line of (2.1). *)
  rapply (magmamap_compose (magmamap_iterated_loops_functor m)).
  (* Target is now the second line of (2.1). *)
  apply equiv_iterated_magma_loops_in.
Defined.

(* A version with group homomorphisms.  May want to make it pointed later. *)
Definition smashing `{Funext} (X Y Z : pType) (n m : nat)
  : (X ->* (Y ->** Z)) -> (Pi n.+1 X ->G Pi m.+1 Y ->A Pi' (m.+2 + n)%nat Z).
(* Again, with wild categories, we'll show that this is a composite of natural transformations. *)
Proof.
  intro f.
  (* Goal is fifth line of equation (2.1) in CS. *)
  apply (equiv_grp_homo_magmamap _ _)^-1%equiv.
  (* Conveniently, [magma_trunc 0 (magma_loops X)] is definitionally equal to [group_to_magma (Pi 1 X)] as magmas. *)
  refine (@magmamap_trunc_rec (magma_loops _) _ 0 _ _).
  rapply (magmamap_compose (smashing_inner Y Z n m)).
  (* Goal is first line of (2.1). *)
  exact (iterated_magma_loops_functor n f).
Defined.

(* TODO: 2.28: show composite is an equivalence under certain hypotheses. *)

(* Note: a bunch of things about concat2 are true for ap011. *)
