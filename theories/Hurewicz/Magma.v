Require Import Basics Types Pointed.
Require Import Algebra.Groups.
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

Definition issig_magmamap X Y : _ <~> MagmaMap X Y := ltac:(issig).

Definition path_magmamap_hset `{Funext} {X Y : Magma} {f g : MagmaMap X Y}
  `{IsHSet Y}
  : f == g -> f = g.
Proof.
  intro p.
  record_equality_hprop.
  by apply path_forall.
Defined.

Definition magmamap_compose {X Y Z : Magma}
  (f : MagmaMap Y Z) (g : MagmaMap X Y) : MagmaMap X Z.
Proof.
  (* Typeclass resolution finds [compose_sg_morphism]. *)
  srapply (Build_MagmaMap _ _ (f o g)).
Defined.

Definition magmamap_compose_assoc `{Funext} {W X Y Z : Magma}
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
           (r : IsSemiGroupPreserving f) : MagmaEquiv X Y
  := (Build_MagmaEquiv X Y (Build_MagmaMap X Y f r) e).

Definition path_magmaequiv `{Funext} {X Y : Magma} (f g : MagmaEquiv X Y)
  : (magmamap f = magmamap g) <~> (f = g).
Proof.
  refine (_^-1 oE _).
  - apply (equiv_ap' (issig_magmaequiv _ _)^-1).
  - simpl.
    exact (equiv_path_sigma_hprop (magmamap f; magmamap_isequiv f) (magmamap g; magmamap_isequiv g)).
Defined.

Definition issig_magmaequiv' (X Y : Magma) :
  {f : X <~> Y & IsSemiGroupPreserving f} <~> MagmaEquiv X Y.
Proof.
  srapply equiv_adjointify.
  - intros [[f e] r]; exact (build_magmaequiv f e r).
  - intros [[f r] e]; exact ((Build_Equiv _ _ f e); r).
  - simpl. reflexivity.
  - simpl. reflexivity.
Defined.

(* This verifies that we have the right notion of equivalence of magmas. *)
Definition equiv_magmaequiv_path `{Univalence} (X Y : Magma)
  : MagmaEquiv X Y <~> (X = Y).
Proof.
  refine (_ oE (issig_magmaequiv' X Y)^-1).
  revert X Y; apply (equiv_path_issig_contr issig_magma); cbn; intros [X m].
  - exists equiv_idmap.  intros x0 x1.  reflexivity.
  - contr_sigsig X (equiv_idmap X).
    exact (@contr_equiv' _ _
           (equiv_functor_sigma_id (fun f => equiv_path_forall11 _ _))^-1
           (contr_basedpaths _)).
Defined.

Definition magma_idmap (X : Magma) : MagmaEquiv X X.
Proof.
  srapply (build_magmaequiv idmap).
Defined.

Definition magmamap_compose_f1 `{Funext} {X Y : Magma} (f : MagmaMap X Y)
  : magmamap_compose f (magma_idmap X) = f.
Proof.
  record_equality.
  - reflexivity.
  - funext x0 x1.
    apply concat_1p.
Defined.

Definition magmamap_compose_1f `{Funext} {X Y : Magma} (f : MagmaMap X Y)
  : magmamap_compose (magma_idmap Y) f = f.
Proof.
  record_equality.
  - reflexivity.
  - funext x0 x1.
    refine (_ @ _).
    1:apply concat_p1.
    apply ap_idmap.
Defined.

Definition magmaequiv_compose {X Y Z : Magma} (g : MagmaEquiv Y Z) (f : MagmaEquiv X Y)
  : MagmaEquiv X Z.
Proof.
  srapply (build_magmaequiv (g oE f)).
  srapply compose_sg_morphism.
Defined.

Definition magmaequiv_inverse {X Y : Magma} (f : MagmaEquiv X Y) : MagmaEquiv Y X.
Proof.
  srapply (build_magmaequiv (magmaequiv_to_equiv f)^-1).
Defined.

(* The left inverse law.  Much trickier than I expected.  Would be easier with univalence. *)
Definition mecompose_eV `{Funext} {X Y : Magma} (f : MagmaEquiv X Y)
  : magmaequiv_compose f (magmaequiv_inverse f) = magma_idmap _.
Proof.
  destruct f as [[f r] e].
  record_equality_hprop.
  change (magmamap_map (Build_MagmaMap X Y f r)) with f in *.
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

(* This also follows directly from Magma Univalence. *)
Definition equiv_magmamap `{Funext} {X Y : Magma} (Z : Magma)
  (e : MagmaEquiv X Y) : MagmaMap Y Z <~> MagmaMap X Z.
Proof.
  srapply equiv_adjointify.
  + exact (fun f => magmamap_compose f e).
  + exact (fun g => magmamap_compose g (magmaequiv_inverse e)).
  + intro f.
    refine (_ @ _).
    1:apply magmamap_compose_assoc.
    refine ((ap (magmamap_compose f) (ap magmamap (mecompose_Ve e))) @ _).
    apply magmamap_compose_f1.
  + intro g.
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
  + intro f.
    refine (_ @ _).
    1:symmetry; apply magmamap_compose_assoc.
    refine ((ap (fun g => magmamap_compose g f) (ap magmamap (mecompose_eV e))) @ _).
    apply magmamap_compose_1f.
  + intro g.
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
  + exact (loops_functor_pp f).
Defined.

(* It would be nice to replace [==] with [=] here, so that we know the
   magmamap structures agree as well.  That leads to a complicated
   goal, but I would guess that with some pencil-and-paper work first,
   it could be wrangled into something doable. We need this stronger
   statement to prove naturality. We actually just need it for the iterated
   version that is proved independently. *)
Definition magma_loops_functor_compose {X Y Z : pType} (f : Y ->* Z) (g : X ->* Y)
  : magma_loops_functor (f o* g)
    == magmamap_compose (magma_loops_functor f) (magma_loops_functor g).
Proof.
  refine (pointed_htpy (loops_functor_compose _ _)).
  (* Coq couldn't find the coercion from [==*] to [==] automatically. *)
Defined.

Definition iterated_magma_loops_functor {X Y : pType} (n : nat)
  : (X ->* Y) -> MagmaMap (iterated_magma_loops n X) (iterated_magma_loops n Y).
Proof.
  intro f.
  snrapply Build_MagmaMap.
  + exact (iterated_loops_functor n.+1 f).
  + exact (iterated_loops_functor_pp f n).
Defined.

Definition iterated_magma_loops_functor_compose {X Y Z : pType} (n : nat)
  (f : Y ->* Z) (g : X ->* Y) : iterated_magma_loops_functor n (f o* g)
  == magmamap_compose (iterated_magma_loops_functor n f)
      (iterated_magma_loops_functor n g).
Proof.
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
  + intro f.
    srapply (Build_GroupHomomorphism f).
    apply (magmamap_op_preserving f).
  + cbn; reflexivity.
  + intro f.
    destruct f as [f p].
    unfold Build_GroupHomomorphism.
    cbn.  apply ap.
    srapply path_ishprop.
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
  - intros x y. reflexivity.
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
    apply (istrunc_equiv_istrunc _ (unfold_iterated_loops' _ _)^-1).
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
  by pointed_reduce.  (* Can this be sped up? *)
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
Definition equiv_semigrouppreserving `{Funext}
           (O : ReflectiveSubuniverse)
           {A B C : Magma} `{In O C}
           (f : MagmaMap A B) `{IsConnMap O _ _ f} (g : B -> C)
  : IsSemiGroupPreserving g <~> IsSemiGroupPreserving (g o f).
Proof.
  unfold IsSemiGroupPreserving.
  refine (_ oE _).
  2: rapply (equiv_o_conn_map O f).
  refine (_ oE _).
  2: { rapply equiv_functor_forall_id; intro a.
       rapply (equiv_o_conn_map O f). }
  rapply equiv_functor_forall_id; intro a1.
  rapply equiv_functor_forall_id; intro a2.
  apply equiv_concat_l.
  apply (ap g).
  apply (magmamap_op_preserving f).
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
  - rapply tr0_inverts_loops_ptr.
  - apply inO_tr_istrunc.
    rapply ishset_iterated_magma_loops.
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
    nrapply (equiv_semigrouppreserving 0%trunc (loops_ptr n X) g).
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
    (* Make typeclass resolution faster in next line. *)
    pose (HS := ishset_iterated_magma_loops n (X:=Y)).
    apply path_magmamap_hset.
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
    (* Make typeclass resolution faster in next line. *)
    pose (HS := ishset_iterated_magma_loops n (X:=Y)).
    apply path_magmamap_hset.
    apply iterated_magma_loops_functor_compose. }
  (** The left map is an equivalence *)
  2: exact _.
  (** The bottom map is an equivalence *)
  1: snrapply isequiv_iterated_magma_loops_conn_trunc; exact _. (* Faster this way than with [srapply]. *)
  (** The right map is an equivalence *)
  apply isequiv_magmamap_postcompose.
  apply isequiv_iterated_loops_cover_proj.
Defined.

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

Definition ap_const' {A B : Type} {x y : A} (p : x = y) (f : A -> B) {b : B}
  (q : forall a, f a = b) : ap f p = q x @ (q y)^.
Proof.
  destruct p.
  symmetry.
  apply concat_pV.
Defined.

(** Not sure if we can simplify this lemma. It is just a generalization of path algebra in [magma_loops_to_magma_loops_pmap] so we can prove it by path induction. Unfortunately, generalizing this causes complication... *)
Definition ap011_ap_const' {A B : Type} {x x' x'' : A}
  (p : x = x') (q : x' = x'') (g : A -> B) {r : B} (h : forall a : A, g a = r)
  : (((ap_const' (p @ q) g h @ ap (concat (h x)) (concat_1p (h x'')^)^) @
    ap (concat (h x)) (ap (fun x0 : r = r => x0 @ (h x'')^) (concat_Vp (h x'))^)) @
    ap (concat (h x)) (concat_pp_p (h x')^ (h x') (h x'')^)) @
    concat_p_pp (h x) (h x')^ (h x' @ (h x'')^) =
    ap_pp g p q @ ap011 concat (ap_const' p g h) (ap_const' q g h).
Proof.
  destruct p, q; cbn.
  by destruct (h x).
Defined.

Definition magma_loops_to_magma_loops_pmap `{Funext} {Y Z : pType}
  : MagmaMap (magma_loops (Y ->** Z)) (magma_loops_pmap Y Z).
Proof.
  snrapply Build_MagmaMap.
  + change (loops (Y ->** Z) -> (Y ->* loops Z)).
    intro p.
    srapply Build_pMap.
    { intro y.
      exact (ap (fun f : Y ->* Z => pointed_fun f y) p). }
    srapply (ap_const' p _ point_eq).
  + intros p q.
    srapply path_pforall.
    srapply Build_pHomotopy; cbn.
    { intro y.
      exact (ap_pp _ p q). }
    simpl.
    symmetry.
    unfold sg_op.
Abort.
(* The path algebra has changed here.  We can fix it later if needed.
    refine (_ @ ap011_ap_const' p q (fun f : Y ->* Z => f (point Y)) point_eq).
    simpl.
    symmetry.
    do 3 refine (concat_p1 _ @ _).
    apply concat_p1.
Defined.
 *)
