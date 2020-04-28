(* A variant of magmas, where the maps only have to *merely* preserve the operation.  Temporarily calling them PreGroups, but haven't changed the name in most places to keep the diff small. And maybe they should just be called magmas? The idea is that in the case where X and Y are groups, these pregroup maps still coincide with group homomorphisms. But in the general situation, it's much easier to prove things about them. For example, the proof the Omega^n is functorial is easy in this setting. *)

Require Import Basics Types Pointed.
Require Import WildCat.
Require Import Algebra.Group.
Require Import Truncations.
Require Import PathAny.
Require Import HoTT.Tactics.
Require Import Hurewicz.ConnCover.

Local Open Scope pointed_scope.

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

Record Magma := {
  magma_type :> Type;
  magma_op :> SgOp magma_type;
}.

Existing Instance magma_op.

Definition issig_magma : _ <~> Magma := ltac:(issig).

Class IsPreGroupPreserving {A B : Type} {Aop : SgOp A} {Bop : SgOp B} (f : A -> B) :=
  merely_preserves_sg_op : merely (IsSemiGroupPreserving f).

Global Instance ishprop_ispregrouppreserving {A B : Type} {Aop : SgOp A} {Bop : SgOp B} (f : A -> B)
  : IsHProp (IsPreGroupPreserving f) := istrunc_truncation _ _.

Section PreGroupMap.

  Context {A B C : Type} {Aop : SgOp A} {Bop : SgOp B} {Cop : SgOp C}
    (f : A -> B) (g : B -> C).

  (** These results follow from the analogous results for IsSemiGroupPreserving, which are found by typeclass search. *)
  Global Instance id_pg_morphism : IsPreGroupPreserving (@id A).
  Proof.
    rapply tr.
  Defined.

  (** Making these global instances causes typeclass loops.  Instead they are declared below as [Hint Extern]s that apply only when the goal has the specified form. *)
  Local Instance compose_pg_morphism : IsPreGroupPreserving f -> IsPreGroupPreserving g ->
    IsPreGroupPreserving (g ∘ f).
  Proof.
    cbn.
    intros fp gp.
    strip_truncations; rapply tr.
  Defined.

  Local Instance invert_pg_morphism
    : forall `{!IsEquiv f}, IsPreGroupPreserving f ->
      IsPreGroupPreserving (f^-1).
  Proof.
    intros E fp; cbn in *.
    strip_truncations; rapply tr.
  Defined.

End PreGroupMap.

Hint Extern 4 (IsPreGroupPreserving (_ ∘ _)) =>
  class_apply @compose_pg_morphism : typeclass_instances.
Hint Extern 4 (IsPreGroupPreserving (_ o _)) =>
  class_apply @compose_pg_morphism : typeclass_instances.
Hint Extern 4 (IsPreGroupPreserving (_^-1)) =>
  class_apply @invert_pg_morphism : typeclass_instances.

Record MagmaMap (X Y : Magma) := {
  magmamap_map : X -> Y;
  magmamap_op_preserving : IsPreGroupPreserving magmamap_map;
}.

Arguments magmamap_map {_ _}.
Arguments magmamap_op_preserving {_ _}.

(** Any magma map can be coerced to the underlying map of types. *)
Coercion magmamap_map : MagmaMap >-> Funclass.

(** We want typeclass search to see such a map is operation preserving. *)
Global Existing Instance magmamap_op_preserving.

Definition issig_magmamap X Y : _ <~> MagmaMap X Y := ltac:(issig).

Definition path_magmamap {X Y : Magma} {f g : MagmaMap X Y}
  : (magmamap_map f = magmamap_map g) <~> (f = g).
Proof.
  refine (_^-1 oE _).
  - apply (equiv_ap' (issig_magmamap _ _)^-1).
  - simpl.
    exact (equiv_path_sigma_hprop (magmamap_map f; magmamap_op_preserving f) (magmamap_map g; magmamap_op_preserving g)).
Defined.

Global Instance isgraph_magma : IsGraph Magma
  := Build_IsGraph Magma MagmaMap.

Definition magmamap_compose {X Y Z : Magma}
  (f : MagmaMap Y Z) (g : MagmaMap X Y) : MagmaMap X Z.
Proof.
  (* Typeclass resolution finds [compose_pg_morphism]. *)
  srapply (Build_MagmaMap _ _ (f o g)).
Defined.

Definition magmamap_compose_assoc {W X Y Z : Magma}
  (f : MagmaMap Y Z) (g : MagmaMap X Y) (h : MagmaMap W X)
  : magmamap_compose (magmamap_compose f g) h = magmamap_compose f (magmamap_compose g h).
Proof.
  record_equality_hprop.
  reflexivity.
Defined.

Record MagmaEquiv (X Y : Magma) := {
  magmamap :> MagmaMap X Y;
  magmamap_isequiv : IsEquiv (magmamap_map magmamap);
}.

Arguments magmamap {X Y} _.
Arguments magmamap_isequiv {X Y} _.

Definition issig_magmaequiv X Y : _ <~> MagmaEquiv X Y := ltac:(issig).

Definition magmaequiv_to_equiv {X Y : Magma} : MagmaEquiv X Y -> Equiv X Y
  := fun f => Build_Equiv _ _ f (magmamap_isequiv f).

Coercion magmaequiv_to_equiv : MagmaEquiv >-> Equiv.

Definition build_magmaequiv {X Y : Magma} (f : X -> Y) (e : IsEquiv f)
           (r : IsPreGroupPreserving f) : MagmaEquiv X Y
  := (Build_MagmaEquiv X Y (Build_MagmaMap X Y f r) e).

(** This needs [Funext] to know that [IsEquiv] is a proposition. *)
Definition path_magmaequiv `{Funext} {X Y : Magma} (f g : MagmaEquiv X Y)
  : (magmamap f = magmamap g) <~> (f = g).
Proof.
  refine (_^-1 oE _).
  - apply (equiv_ap' (issig_magmaequiv _ _)^-1).
  - simpl.
    exact (equiv_path_sigma_hprop (magmamap f; magmamap_isequiv f) (magmamap g; magmamap_isequiv g)).
Defined.

Definition issig_magmaequiv' (X Y : Magma) :
  {f : X <~> Y & IsPreGroupPreserving f} <~> MagmaEquiv X Y.
Proof.
  srapply equiv_adjointify.
  - intros [[f e] r]; exact (build_magmaequiv f e r).
  - intros [[f r] e]; exact ((Build_Equiv _ _ f e); r).
  - simpl. reflexivity.
  - simpl. reflexivity.
Defined.

(** Another variant, not currently used. *)
Definition path_magmaequiv' {X Y : Magma} (f g : MagmaEquiv X Y)
  : (magmaequiv_to_equiv f = magmaequiv_to_equiv g) <~> (f = g).
Proof.
  refine (_^-1 oE _).
  - apply (equiv_ap' (issig_magmaequiv' _ _)^-1).
  - simpl.
    exact (equiv_path_sigma_hprop
             (magmaequiv_to_equiv f; magmamap_op_preserving f)
             (magmaequiv_to_equiv g; magmamap_op_preserving g)).
Defined.

(* This verifies that we have the right notion of equivalence of magmas. *)
(* It is very unlikely to be true with our new definitions. *)
Definition equiv_magmaequiv_path `{Univalence} (X Y : Magma)
  : MagmaEquiv X Y <~> (X = Y).
Proof.
  refine (_ oE (issig_magmaequiv' X Y)^-1).
  revert X Y; apply (equiv_path_issig_contr issig_magma); cbn; intros [X m].
  - exists equiv_idmap.  rapply tr.
  - contr_sigsig X (equiv_idmap X).
    Fail exact (@contr_equiv' _ _
           (equiv_functor_sigma_id (fun f => equiv_path_forall11 _ _))^-1
           (contr_basedpaths _)).
Abort.

Definition magma_idmap (X : Magma) : MagmaEquiv X X.
Proof.
  srapply (build_magmaequiv idmap).
Defined.

Definition magmamap_compose_f1 {X Y : Magma} (f : MagmaMap X Y)
  : magmamap_compose f (magma_idmap X) = f.
Proof.
  apply path_magmamap.
  reflexivity.
Defined.

Definition magmamap_compose_1f {X Y : Magma} (f : MagmaMap X Y)
  : magmamap_compose (magma_idmap Y) f = f.
Proof.
  apply path_magmamap.
  reflexivity.
Defined.

Global Instance is01cat_magma : Is01Cat Magma
  := Build_Is01Cat _ _ magma_idmap (@magmamap_compose).

Definition magmaequiv_compose {X Y Z : Magma} (g : MagmaEquiv Y Z) (f : MagmaEquiv X Y)
  : MagmaEquiv X Z.
Proof.
  srapply (build_magmaequiv (g oE f)).
  rapply compose_pg_morphism.
Defined.

Definition magmaequiv_inverse {X Y : Magma} (f : MagmaEquiv X Y) : MagmaEquiv Y X.
Proof.
  srapply (build_magmaequiv (magmaequiv_to_equiv f)^-1).
Defined.

(** The left inverse law. *)
Definition mecompose_eV `{Funext} {X Y : Magma} (f : MagmaEquiv X Y)
  : magmaequiv_compose f (magmaequiv_inverse f) = magma_idmap _.
Proof.
  apply path_magmaequiv, path_magmamap.
  cbn.
  apply path_forall; intro; apply eisretr.
Defined.

(** The right inverse law. *)
Definition mecompose_Ve `{Funext} {X Y : Magma} (f : MagmaEquiv X Y)
  : magmaequiv_compose (magmaequiv_inverse f) f = magma_idmap _.
Proof.
  apply path_magmaequiv, path_magmamap.
  cbn.
  apply path_forall; intro; apply eissect.
Defined.

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

Definition magma_loops (X : pType) : Magma
  := Build_Magma (loops X) concat.

(** This is for n.+1 since at n=0 no magma to be found. *)
Definition iterated_magma_loops (n : nat) (X : pType) : Magma
  := Build_Magma (iterated_loops (S n) X) concat.

Definition magma_loops_functor {X Y : pType}
  : (X ->* Y) -> MagmaMap (magma_loops X) (magma_loops Y).
Proof.
  intro f.
  snrapply Build_MagmaMap.
  + exact (loops_functor f).
  + exact (tr (loops_functor_pp f)).
Defined.

(* We don't use this, just the iterated version that is proved without this. *)
Definition magma_loops_functor_compose `{Funext} {X Y Z : pType} (f : Y ->* Z) (g : X ->* Y)
  : magma_loops_functor (f o* g)
    = magmamap_compose (magma_loops_functor f) (magma_loops_functor g).
Proof.
  apply path_magmamap.
  apply path_forall.
  refine (pointed_htpy (loops_functor_compose _ _)).
  (* Coq couldn't find the coercion from [==*] to [==] automatically. *)
Defined.

Definition iterated_magma_loops_functor {X Y : pType} (n : nat)
  : (X ->* Y) -> MagmaMap (iterated_magma_loops n X) (iterated_magma_loops n Y).
Proof.
  intro f.
  snrapply Build_MagmaMap.
  + exact (iterated_loops_functor n.+1 f).
  + exact (tr (iterated_loops_functor_pp f n)).
Defined.

Definition iterated_magma_loops_functor_compose `{Funext} {X Y Z : pType} (n : nat)
  (f : Y ->* Z) (g : X ->* Y) : iterated_magma_loops_functor n (f o* g)
  = magmamap_compose (iterated_magma_loops_functor n f)
      (iterated_magma_loops_functor n g).
Proof.
  apply path_magmamap.
  apply path_forall.
  refine (pointed_htpy (iterated_loops_functor_compose _ _ _ _ _ _)).
  (* Coq couldn't find the coercion from [==*] to [==] automatically. *)
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
  {f : X ->* Y} : IsEquiv f -> MagmaEquiv (iterated_magma_loops n X) (iterated_magma_loops n Y).
Proof.
  intro e.
  srapply (Build_MagmaEquiv _ _ (iterated_magma_loops_functor n f)).
Defined.

Definition group_to_magma : Group -> Magma
  := fun G => Build_Magma G _.

Coercion group_to_magma : Group >-> Magma.

Definition equiv_grp_homo_magma_map `{F : Funext} (G H : Group)
  : GroupHomomorphism G H <~> MagmaMap G H.
Proof.
  srapply equiv_adjointify.
  + intro f.
    srapply (Build_MagmaMap G H f).
    rapply tr.
  + intros [f r].
    srapply (Build_GroupHomomorphism f).
    strip_truncations.
    exact r.
  + intro f.
    record_equality_hprop.
    reflexivity.
  + intros [f r].
    record_equality_hprop.
    reflexivity.
Defined.

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
  - apply tr. intros x y. reflexivity.
Defined.

Global Instance isequiv_magmamap_precompose `{Funext} {A B C : Magma}
  (f : MagmaMap A B)
  : IsEquiv f -> IsEquiv (fun g : MagmaMap B C => magmamap_compose g f).
Proof.
  intro e.
  set (fe := Build_MagmaEquiv _ _ f e).
  exact (equiv_isequiv (equiv_magmamap C fe)).
Defined.

Global Instance isequiv_magmamap_postcompose `{Funext} {A B C : Magma}
  (f : MagmaMap B C)
  : IsEquiv f -> IsEquiv (fun g : MagmaMap A B => magmamap_compose f g).
Proof.
  intro e.
  set (fe := Build_MagmaEquiv _ _ f e).
  refine (equiv_isequiv (equiv_magmamap' A fe)).
Defined.

(** BVR 5.1 *)
(* TODO: should state this using groups, not magmas, and use [equiv_grp_homo_magma_map] to recover this form. *)
Theorem isequiv_iterated_magma_loops_conn_trunc
  (n : nat) (X Y : pType) `{IsConnected n X} `{IsConnected n Y} `{IsTrunc n.+1 X} `{IsTrunc n.+1 Y}
  : IsEquiv (@iterated_magma_loops_functor X Y n).
Proof.
Admitted.

(* Several of the next things should be in Loops.v or pTrunc.v.
   This one could be generalized to two truncation levels. *)
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

Definition pfiber_loops_functor {A B : pType} (f : A ->* B)
  : loops (pfiber f) <~>* pfiber (loops_functor f).
Proof.
  srapply Build_pEquiv'.
  { symmetry.
    etransitivity.
    2: srapply equiv_path_sigma.
    simpl; unfold hfiber.
    srapply equiv_functor_sigma_id.
    intro p; cbn.
    refine (_ oE _).
    { rapply equiv_concat_l.
      apply transport_paths_Fl. }
    refine (_ oE equiv_moveL_Mp _ _ _).
    refine (equiv_moveR_Vp _ _ _ oE _).
    refine (_ oE _).
    2: { rapply equiv_concat_r.
         apply concat_p1. }
    apply equiv_path_inverse. }
  (* Manually applying [pointed_reduce_pmap], since the last [cbn] is slow. *)
  destruct B as [B b0], f as [f ptd].
  cbn in f, ptd; destruct ptd.
  reflexivity.
Defined.

Definition pfiber_iterated_loops_functor {A B : pType} (n : nat) (f : A ->* B)
  : iterated_loops n (pfiber f) <~>* pfiber (iterated_loops_functor n f).
Proof.
  induction n.
  1: reflexivity.
  refine (pfiber_loops_functor _ o*E _).
  apply pequiv_loops_functor.
  apply IHn.
Defined.

(* When we have an appropriate dependent elimination along a map [f], composing with [f] gives an equivalence between magmamap structures.  The assumption can be weakened to only having [f] an O-equivalence, but the main library will need a result similar to [equiv_o_conn_map] to show this. *)
(* If we weakened our definition of [IsPreGroupPreserving] to [forall a b, merely (f (a * b) = f a * f b], then no assumption on [C] would be needed, and we just need that [f] is (-1)-connected (or even just a (-1)-equivalence). *)
Definition equiv_pregrouppreserving `{Funext}
           (O : ReflectiveSubuniverse)
           {A B C : Magma} `{In O C}
           (f : MagmaMap A B) `{IsConnMap O _ _ f} (g : B -> C)
  : IsPreGroupPreserving g <~> IsPreGroupPreserving (g o f).
Proof.
  destruct f as [f r].
  (* Four lines inserted to convert proof from IsSemiGroupPreserving to IsPreGroupPreserving. There's probably a shorter direct proof. *)
  cbn in H1.
  unfold IsPreGroupPreserving in *.
  strip_truncations.
  apply equiv_O_functor.
  (* The original proof continues. *)
  unfold IsSemiGroupPreserving; cbn.
  refine (_ oE _).
  2: rapply (equiv_o_conn_map O f).
  refine (_ oE _).
  2: { rapply equiv_functor_forall_id; intro a.
       rapply (equiv_o_conn_map O f). }
  cbn.
  rapply equiv_functor_forall_id; intro a1.
  rapply equiv_functor_forall_id; intro a2.
  apply equiv_concat_l.
  apply (ap g).
  apply r.
Defined.

(* Now we work towards [isequiv_iterated_magma_loops_functor_conn_trunc'], which generalizes the BVR result [isequiv_iterated_magma_loops_functor_conn_trunc].  We need some results about the map [loops_ptr]. *)

(* Warning: magma_loops indexing is one off from loops, so this is the (n+1)-fold loop functor. *)
Local Definition loops_ptr (n : nat) (X : pType)
  := (iterated_magma_loops_functor n (@ptr n.+1 X)).

Local Definition precompose_loops_ptr (n : nat) (X : pType) (Y : pType)
  : ((iterated_loops n.+1 (pTr n.+1 X)) -> (iterated_loops n.+1 Y))
    -> ((iterated_loops n.+1 X) -> (iterated_loops n.+1 Y))
  := fun g => g o (loops_ptr n X).

Local Instance zero_conn_loops_ptr `{Univalence} (n : nat)
           (X : pType) `{IsConnected n X}
  : IsConnMap 0%nat (loops_ptr n X).
Proof.
  apply isconnected_iterated_loops_functor.
  rewrite <- trunc_index_inc_agree.
  (* [trunc_index_inc 0 n.+1] is definitionally [n.+1]. *)
  exact _.
Defined.

Local Definition tr0_inverts_loops_ptr `{Univalence} (n : nat)
           (X : pType) `{IsConnected n X}
  : O_inverts 0%trunc (loops_ptr n X).
Proof.
  apply O_inverts_conn_map.
  rapply zero_conn_loops_ptr.
Defined.

Local Definition isequiv_precompose_loops_ptr `{Univalence} (n : nat)
           (X : pType) `{IsConnected n X}
           (Y : pType) `{IsTrunc n.+1 Y}
  : IsEquiv (precompose_loops_ptr n X Y).
Proof.
  snrapply (isequiv_precompose_O_inverts 0%trunc _).
  - exact _.  (* Funext *)
  - rapply tr0_inverts_loops_ptr.
  - rapply ishset_iterated_magma_loops.
    (* [exact _] works, but is slow. *)
Defined.

(* Now want the same thing, but for types of magma maps. *)
Local Definition equiv_precompose_magma_loops_ptr `{Univalence} (n : nat)
           (X : pType) `{IsConnected n X}
           (Y : pType) `{IsTrunc n.+1 Y}
  : (MagmaMap (iterated_magma_loops n (pTr n.+1 X)) (iterated_magma_loops n Y))
    <~> (MagmaMap (iterated_magma_loops n X) (iterated_magma_loops n Y)).
Proof.
  refine ((issig_magmamap _ _) oE _ oE (issig_magmamap _ _)^-1).
  snrapply equiv_functor_sigma'.
  - nrapply Build_Equiv.  rapply isequiv_precompose_loops_ptr.
  - intro g; cbn.
    nrapply (equiv_pregrouppreserving 0%trunc (loops_ptr n X) g).
    + exact _.  (* Funext *)
    + rapply ishset_iterated_magma_loops. (* Found by typeclass inference, but slow. *)
    + rapply zero_conn_loops_ptr.         (* Found by typeclass inference, but slow. *)
Defined.

Global Instance isequiv_iterated_magma_loops_functor_conn_trunc' `{Univalence} (n : nat)
  (X : pType) `{IsConnected n X}
  (Y : pType) `{IsTrunc n.+1 Y}
  : IsEquiv (@iterated_magma_loops_functor X Y n).
Proof.
  (** We prove this is an equivalence by constructing a commutative square of equivalences *)
  snrapply isequiv_commsq.
  (** Bottom left corner *)
  1: exact (pTr n.+1 X ->* Y).
  (** Bottom right corner *)
  1: exact (MagmaMap (iterated_magma_loops n (pTr n.+1 X))
    (iterated_magma_loops n Y)).
  (** Bottom horizontal map *)
  1: exact (iterated_magma_loops_functor n).
  (** Left vertical map is [fun f => f o* ptr], but we hint that it's an equivalence: *)
  1: apply equiv_ptr_rec.
  (** Right vertical map *)
  1: rapply equiv_precompose_magma_loops_ptr.
  (** The square commutes by functoriality of iterated_magma_loops *)
  { symmetry.
    intro f.
    rapply iterated_magma_loops_functor_compose. }
  (** Immediately we have some equivalences. *)
  2,3: exact _.
  (** To prove this final map is an equivalence we use another commutative square. *)
  snrapply isequiv_commsq.
  (** The bottom left type *)
  1: exact (pTr n.+1 X ->* cover n Y).
  (** The bottom right type *)
  1: exact (MagmaMap (iterated_magma_loops n (pTr n.+1 X))
    (iterated_magma_loops n (cover n Y))).
  (** The bottom map *)
  1: exact (iterated_magma_loops_functor n).
  (** The left map *)
  { apply equiv_fun.
    apply equiv_postcompose_cover_proj.
    exact _. }
  (** The right map *)
  { intro g.
    srapply (magmamap_compose _ g).
    apply iterated_magma_loops_functor.
    apply cover_proj. }
  (** The square commutes by functoriality of iterated_magma_loops *)
  { cbn.
    symmetry.
    intro f.
    apply iterated_magma_loops_functor_compose. }
  (** The left map is an equivalence *)
  2: exact _.
  (** The bottom map is an equivalence *)
  1: snrapply isequiv_iterated_magma_loops_conn_trunc; exact _. (* Faster this way than with [srapply]. *)
  (** The right map is an equivalence *)
  apply isequiv_magmamap_postcompose.
  apply isequiv_iterated_loops_cover_proj.
Defined.

(** The type of pointed maps [Y ->* Omega Z] is a magma under pointwise operations. *)
(** TODO: Remove this if it is unneeded. *)
Definition magma_loops_pmap (Y Z : pType) : Magma.
Proof.
  snrefine (Build_Magma (Y ->* Build_pType (magma_loops Z) idpath) _).
  intros f g.
  srapply Build_pMap.
  { intro y.
    exact (sg_op (f y) (g y)). }
  simpl.
  refine (ap011 _ (point_eq _) (point_eq _)).
Defined.

(** To express naturality, it's probably better to consider a category of pointed magmas. OTOH, a few things would be simpler if we stuck to the special case of loops.  Not sure yet what to do. *)
Record pMagma := {
  pmagma_magma : Magma;
  pmagma_pointed : pmagma_magma;
  pmagma_idem : sg_op pmagma_pointed pmagma_pointed = pmagma_pointed
}.

Coercion pmagma_magma : pMagma >-> Magma.

Definition ptype_pmagma (Z : pMagma) : pType
  := Build_pType Z (pmagma_pointed Z).

Coercion ptype_pmagma : pMagma >-> pType.

Definition pmagma_loops (Z : pType) : pMagma
  := Build_pMagma (magma_loops Z) idpath idpath.

(** The type of pointed maps [Y ->* Z] is a magma under pointwise operations when [Z] is a pointed magma. *)
Definition magma_pmagma_pmap (Y : pType) (Z : pMagma): Magma.
Proof.
  snrefine (Build_Magma (Y ->* Z) _).
  intros f g.
  srapply (Build_pMap _ _ (fun y => sg_op (f y) (g y))).
  simpl.
  refine (ap011 _ (point_eq _) (point_eq _) @ pmagma_idem _).
Defined.

(** [phomotopy_path] sends concatenation to composition of pointed homotopies.*)
(** TODO: move to pHomotopy.v. *)
Definition phomotopy_path_pp_aspath {A : pType} {P : pFam A}
  {f g h : pForall A P} (p : f = g) (q : g = h)
  : phomotopy_path (p @ q) = phomotopy_path p @* phomotopy_path q.
Proof.
  pointed_reduce.  reflexivity.
Defined.

(** TODO: move to pHomotopy.v. *)
Global Instance isequiv_phomotopy_path `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
  : IsEquiv (@phomotopy_path A P f g).
Proof.
  rapply (transport IsEquiv).
  - symmetry; rapply path_equiv_path_pforall_phomotopy_path.
  - exact _.
Defined.

(** This is just to illustrate that the general operation we defined on the type of pointed maps to a pointed magma [W] agrees definitionally with composition of pointed homotopies in the case that [W] is [loops Z] for some [Z]. We first see that the types agree by defining the identity map between them. *)
Local Definition types_map {Y Z : pType}
  : magma_type (magma_pmagma_pmap Y (pmagma_loops Z)) -> (@pconst Y Z ==* @pconst Y Z)
  := idmap.

(** We need to insert this identity map or do other things in order for Coq to correctly parse the claim that [sg_op p q = p @* q]. *)
Local Definition ops_agree {Y Z : pType} (p q : magma_pmagma_pmap Y (pmagma_loops Z))
  : types_map (sg_op p q) = (types_map p) @* (types_map q).
Proof.
  unfold "@*"; cbn; unfold point_eq.
  reflexivity.
  (* This works because of two things.  First, note that given {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q'), the terms [h @@ h'] and [ap011 concat h h'] are definitionally equal. The main library defines composition using [@@], but we define it using [ap011], since we need to handle any [sg_op], not just [concat].  Second, the parentheses in the definition of [@*] ([phomotopy_transitive]) were arranged so that in this case we get [foo @ (1 @ 1)] which reduces to [foo @ 1], matching what [sg_op] produces. *)
Defined.

Definition magma_loops_in `{Funext} {Y Z : pType}
  : MagmaMap (magma_loops (Y ->** Z)) (magma_pmagma_pmap Y (pmagma_loops Z)).
Proof.
  snrapply Build_MagmaMap.
  - rapply phomotopy_path.
  - apply tr.
    rapply phomotopy_path_pp_aspath.
Defined.

(* This equivalence is one of the lemmas in the CS Hurewicz paper. *)
Definition equiv_magma_loops_in `{Funext} {Y Z : pType}
  : MagmaEquiv (magma_loops (Y ->** Z)) (magma_pmagma_pmap Y (pmagma_loops Z)).
Proof.
  snrapply Build_MagmaEquiv.
  - rapply magma_loops_in.
  - exact _.
Defined.

(** To state naturality, we need the pointed composition maps. *)

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
  record_equality.
  - reflexivity.
  - cbn.
    exact (concat_p1 _ @ ap_const _ _).
(* OR:  pointed_reduce_pmap f; reflexivity. *)
Defined.

Definition pprecompose {A B : pType} (C : pType) (f : A ->* B) :
  (B ->** C) ->* (A ->** C).
Proof.
  simple refine (Build_pMap _ _ _ _).
  - exact (fun g => g o* f).
  - apply postcompose_pconst_as_path.
Defined.

(* TODO: Generalize to dependent functions? *)
Definition phomotopy_path_nat_l {Y Y' Z : pType} (h h' : Y' ->* Z) (f : Y ->* Y') (p : h = h')
  : phomotopy_path (ap (pprecompose Z f) p)
    = (pmap_prewhisker f) (phomotopy_path p).
Proof.
  pointed_reduce; reflexivity.
Defined.

(* Could just inline this where needed. *)
Definition phomotopy_postwhisker `{Funext} {A : pType} {P : pFam A} {f g h : pForall A P}
           (p q : f ==* g) (r : g ==* h) (s : p ==* q)
  : p @* r ==* q @* r.
Proof.
  apply (phomotopy_hcompose s).
  reflexivity.
Defined.

Definition functor2_phomotopy_path `{Funext} {A : pType} {P : pFam A}
  {f f' g g' : pForall A P} (p : f = g) (q : f = f') (r : g = g')
  : phomotopy_path (q^ @ p @ r) ==*
                   phomotopy_path (q^) @* phomotopy_path p @* phomotopy_path r.
Proof.
  refine (_ @* _).
  1: apply phomotopy_path_pp.
  rapply phomotopy_postwhisker.
  apply phomotopy_path_pp.
Defined.

Local Definition phomotopy_path_pconst {Y Y' Z : pType} (f : Y ->* Y')
  : phomotopy_path (postcompose_pconst_as_path f) ==* postcompose_pconst (C:=Z) f.
Proof.
  (* Manually applying [pointed_reduce_pmap], since the last [cbn] is slow. *)
  destruct Y' as [Y' y0'], f as [f ptd].
  cbn in f, ptd; destruct ptd.
  reflexivity.
Defined.

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

Local Definition bottom_composite `{Funext}  {Y Y' Z : pType} (f : Y ->* Y') (p : Y' ->* loops Z)
  : pprecompose (loops Z) f p ==*
    phomotopy_path ((postcompose_pconst_as_path f)^)
                   @* (pmap_prewhisker f (types_map p))
                   @* phomotopy_path (postcompose_pconst_as_path f).
Proof.
  transitivity ((postcompose_pconst f)^*
                @* (pmap_prewhisker f (types_map p))
                @* (postcompose_pconst f)).
  - (* Manually applying [pointed_reduce_pmap] to have shorter names. *)
    destruct Y' as [Y' y0'], f as [f ptd].
    cbn in f, ptd; destruct ptd.
    snrapply Build_pHomotopy.
    + cbn.
      intro y.
      symmetry.  refine (concat_p1 _ @ concat_1p _).
    + unfold types_map.
      destruct p as [p p0]; cbn in *.
      revert p0.
      generalize (p (f (point Y))).
      rapply paths_ind_r.
      reflexivity.
  - (* Not sure why Coq can't guess the type of the next underscore.  We give it a hint. *)
    refine (phomotopy_hcompose (p:=(postcompose_pconst f)^* @* pmap_prewhisker f (types_map p))
                               _ (phomotopy_path_pconst (Z:=Z) f)^*).
    rapply phomotopy_postwhisker.
    symmetry.
    refine (phomotopy_path_V _ @* _).
    exact (phomotopy_inv2 (phomotopy_path_pconst f)).
Defined.

Local Definition top_composite `{Funext} {Y Y' Z : pType} (f : Y ->* Y') (p : loops (Y' ->** Z))
  : loops_functor (pprecompose Z f) p =
    (postcompose_pconst_as_path f)^ @ (ap (pprecompose Z f) p) @ (postcompose_pconst_as_path f).
Proof.
  (* Manually applying [pointed_reduce_pmap], since the last [cbn] is slow. *)
  destruct Y' as [Y' y0'], f as [f ptd].
  cbn in f, ptd; destruct ptd.
  (* [cbn] is slow here, as is [apply concat_p_pp]. *)
  snrapply concat_p_pp.
Defined.

(** The naturality of magma_loops_in in the first variable follows by pasting four regions together in a large diagram. *)
Definition magma_loops_in_nat_l `{Funext} {Y Y' Z : pType} (f : Y ->* Y') (p : magma_loops (Y' ->** Z))
  : magma_loops_in (loops_functor (pprecompose Z f) p)
    = (pprecompose (loops Z) f) (magma_loops_in p).
Proof.
  refine ((ap magma_loops_in (top_composite f p)) @ _).
  apply path_pforall.
  set (ppapf := postcompose_pconst_as_path f).
  refine (_ @* _).
  1:{ unfold magma_loops_in, magmamap_map.
      exact (functor2_phomotopy_path _ ppapf ppapf). }
  refine (_ @* _).
  1:{ apply phomotopy_path.
      nrapply (ap (fun q => (phomotopy_path ppapf^) @* q @* (phomotopy_path ppapf))).
      apply phomotopy_path_nat_l. }
  symmetry.
  apply bottom_composite.
Defined.

(* TODO: Generalize to dependent functions? *)
(* The extra [idpath]s are just to match what we need later, saving some work then. *)
Definition phomotopy_path_nat_r {Y Z Z' : pType} (h h' : Y ->* Z) (f : Z ->* Z') (p : h = h')
  : phomotopy_path (1 @ (ap (fun g => f o* g) p @ 1))
    = (pmap_postwhisker f) (phomotopy_path p).
Proof.
  pointed_reduce; reflexivity.
Defined.

(** The naturality of magma_loops_in in the second variable. *)
Definition magma_loops_in_nat_r `{Funext} {Y Z Z' : pType} (f : Z ->* Z') (p : magma_loops (Y ->** Z))
  : magma_loops_in (loops_functor (ppostcompose Y f) p)
    = (loops_functor f) o* (magma_loops_in p).
  (* Or: ... = ppostcompose Y (loops_functor f) (magma_loops_in p). *)
Proof.
  (* Manually applying [pointed_reduce_pmap] to avoid cbn. *)
  (* Also, want to save reference to the pointed function. *)
  pose (fp := f).
  destruct Z' as [Z' z0'], f as [f ptd].
  cbn in f, ptd; destruct ptd.
  unfold loops_functor, Build_pMap, pointed_fun.
  cbn.
  refine (phomotopy_path_nat_r _ _ fp p @ _).
  apply path_pforall.
  snrapply Build_pHomotopy.
  - intro y.
    cbn.
    exact (concat_1p _ @ concat_p1 _)^.
  - cbn.
    (* The next line is needed to make the [destruct] work. *)
    change (phomotopy_path p) with (phomotopy_path p).
    destruct (phomotopy_path p) as [php php0]; cbn in *.
    revert php0.
    generalize (php (point Y)) as phpY.
    rapply paths_ind_r.
    reflexivity.
Defined.

(* TODO:
   Better definitions of loop_functor and/or postwhisker and/or o* to make this easier?
   Move stuff not involving magmas elsewhere.
*)
