(* -*- mode: coq; mode: visual-line -*- *)
(** * Kan extensions of type families *)

(** ** Part of the formalization of section 4 of the paper: Injective Types in Univalent Mathematics by Martin Escardo. *)
(** Many proofs guided by Martin Escardo's original Agda formalization of this paper which can be found at: https://www.cs.bham.ac.uk/~mhe/TypeTopology/InjectiveTypes.Article.html. *)

Require Import Basics.
Require Import Types.Sigma Types.Unit Types.Forall Types.Empty Types.Universe Types.Equiv.
Require Import HFiber.
Require Import Truncations.Core.
Require Import ReflectiveSubuniverse.


(** Being careful about universe structure for these first few definitions because they are used in the rest of the paper. *)
Section UniverseStructure.
  Universes u v w uv uw vw uvw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
    uv <= uvw, uw <= uvw, vw <= uvw.

  Definition LeftKanTypeFamily@{} {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w}) (j : X -> Y)
    := (fun y => sig@{uv w} (fun w : (hfiber j y) => f (w.1))).

  Definition RightKanTypeFamily@{} {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w}) (j : X -> Y)
    := (fun y => forall w : (hfiber j y), f (w.1)).

  Notation "f <| j" := (LeftKanTypeFamily f j) (at level 40).
  Notation "f |> j" := (RightKanTypeFamily f j) (at level 40).

  (** If [j] is an embedding, then [f <| j] and [f |> j] are extensions in the following sense: [(f <| j o j)x <~> fx <~> (f |> j o j)]. *)
  Definition isext_leftkantypefamily@{} {X : Type@{u}} {Y : Type@{v}}
    (f : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} ((LeftKanTypeFamily@{} f j) (j x)) (f x).
  Proof.
    transparent assert (C : (Contr (hfiber j (j x)))).
    - srapply contr_inhabited_hprop. exact (x; idpath (j x)).
    - snrapply (@equiv_contr_sigma _ _ C).
  Defined.

  Definition isext_rightkantypefamily@{} `{Funext} {X : Type@{u}} {Y : Type@{v}}
    (f : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} ((RightKanTypeFamily@{} f j) (j x)) (f x).
  Proof.
    transparent assert (C : (Contr (hfiber j (j x)))).
    - srapply contr_inhabited_hprop. exact (x; idpath (j x)).
    - snrapply (@equiv_contr_forall _ _ C).
  Defined.

End UniverseStructure.

(** For [y : Y] not in the image of [j], [(f <| j)y] is empty and [(f |> j)y] is. *)
Definition isempty_leftkantypefamily {X : Type@{u}} {Y : Type@{v}}
  (f : X -> Type@{w}) (j : X -> Y) (y : Y) (ynin : forall x : X, j x = y -> Empty)
  : LeftKanTypeFamily f j y -> Empty
  := fun '((x; p); _) => ynin x p.

Definition contr_rightkantypefamily `{Funext} {X : Type@{u}} {Y : Type@{v}}
  (f : X -> Type@{w}) (j : X -> Y) (y : Y) (ynin : forall x : X, j x = y -> Empty)
  : Contr (RightKanTypeFamily f j y).
Proof.
  snrapply contr_forall.
  intros [x p].
  apply (Empty_rec (ynin x p)).
Defined.

Definition equiv_leftkantypefamily {X : Type@{u}} {Y : Type@{v}}
  (f : X -> Type@{w}) (j : X -> Y)
  : {x | f x} <~> {x | LeftKanTypeFamily f j x}.
Proof.
  snrapply equiv_adjointify.
  - apply (fun w : {x | f x} => (j w.1; (w.1; idpath); w.2)).
  - apply (fun '((y; ((x; p); y')) : {x | LeftKanTypeFamily f j x}) => (x; y')).
  - intros [y [[x []] y']]; cbn. reflexivity.
  - intros [x y]; cbn. reflexivity.
Defined.

Definition equiv_rightkantypefamily `{Funext} {X : Type@{u}} {Y : Type@{v}}
  (f : X -> Type@{w}) (j : X -> Y)
  : (forall x, f x) <~> (forall y, (RightKanTypeFamily f j) y).
Proof.
  snrapply equiv_adjointify.
  - intros g y w. apply (g w.1).
  - apply (fun h x => h (j x) (x; idpath)).
  - intros h. apply path_forall. intros y. apply path_forall.
    intros [x []]; cbn. reflexivity.
  - intros g. apply path_forall. intros y. reflexivity.
Defined.
(** Note that these equivalences tell us that [sig (f <| j)] and [forall (f |> j)] can be thought of as just different notation for the sum and product of a type family. *)

(** Here we are taking the perspective of a type family [f : X -> Type] being a sort of oo-presheaf, considering the interpretation of [X] as an oo-ggroupoid and [Type] as a universe of spaces i.e. an appropriate generalization of the category of sets. *)
(** It is easy to see that a type family [f] is functorial if we define its action on paths with [transport]. Functoriality then reduces to known lemmas about the [transport] function. *)

(** We can now define the type of transformations between two type families. *)
Definition ooPresheafTransforms {X : Type@{u}} (f : X -> Type@{w}) (f' : X -> Type@{w'})
  := forall x, (f x) -> (f' x).

Notation "f =< g" := (ooPresheafTransforms f g) (at level 60).

(** It is easy to see that these transformations are automatically natural by their definition. *)

Definition comp_transformation {X} {f g h : X -> Type} (b : g =< h) (a : f =< g)
  : f =< h
  := fun x A => (b x) (a x A).

Definition whisker_transformation {X Y} {f g : Y -> Type} (a : f =< g) (j : X -> Y)
  : f o j =< g o j
  := fun x A => (a (j x) A).

(** If [j] is an embedding then [(f <| j) =< (f |> j)]. *)
Definition transform_leftkantypefam_rightkantypefam {X Y : Type}
  (f : X -> Type) (j : X -> Y) (isem : IsEmbedding j)
  : (LeftKanTypeFamily f j) =< (RightKanTypeFamily f j).
Proof.
  intros y [w' z] w.
  snrapply (transport (fun a => f a.1) _ z).
  srapply path_ishprop.
Defined.

(** Under this interpretation, we can think of the maps [f <| j] and [f |> j] as left and right Kan extentions of [f : X -> Type] along [j : X -> Y]. *)
(** To see this we can construct the (co)unit transformations of our extensions. *)
Definition unit_leftkantypefam {X Y : Type} (f : X -> Type) (j : X -> Y)
  : f =< (LeftKanTypeFamily f j o j)
  := (fun x A => ((x; idpath); A)).
  
Definition counit_rightkantypefam {X Y : Type} (f : X -> Type) (j : X -> Y)
  : (RightKanTypeFamily f j o j) =< f
  := (fun x A => A (x; idpath)).

Definition counit_leftkantypefam {X Y : Type} (g : Y -> Type) (j : X -> Y)
  : LeftKanTypeFamily (g o j) j =< g.
Proof.
  intros y [[x p] C].
  apply (transport g p C).
Defined.

Definition unit_rightkantypefam {X Y : Type} (g : Y -> Type) (j : X -> Y)
  : g =< RightKanTypeFamily (g o j) j.
Proof.
  intros y C [x p].
  apply (transport g p^ C).
Defined.

(** Universal property of the Kan extensions. *)
Definition univ_property_LeftKanTypeFam `{Funext} {X Y} {j : X -> Y}
  {f : X -> Type} {g : Y -> Type} (a : f =< g o j)
  : { b : LeftKanTypeFamily f j =< g | comp_transformation (whisker_transformation b j) (unit_leftkantypefam f j) == a}.
Proof.
  snrefine (_; _).
  - intros y [[x p] A]. apply (p # a x A).
  - intros x. apply path_forall. intros y. reflexivity.
Defined.

(** TODO: Prove uniqueness of the universal property. *)
(*Definition contr_univ_property_LeftKanTypeFam `{Funext} {X Y} {j : X -> Y}
  {f : X -> Type} {g : Y -> Type} {a : f =< g o j}
  : Contr { b : LeftKanTypeFamily f j =< g | comp_transformation (whisker_transformation b j) (unit_leftkantypefam f j) == a}.
Proof.
  apply (Build_Contr _ (univ_property_LeftKanTypeFam a)).
  intros [b F]. srapply path_sigma.
  - apply path_forall. intros y. apply path_forall.
    intros [[w []] c]. srefine (ap10 (F w) c)^.
  - apply path_forall. intros x.
Abort.*)

Definition univ_property_RightKanTypeFam `{Funext} {X Y} {j : X -> Y}
  {f : X -> Type} {g : Y -> Type} (a : g o j =< f)
  : { b : g =< RightKanTypeFamily f j | comp_transformation (counit_rightkantypefam f j) (whisker_transformation b j) == a}.
Proof.
  snrefine (_; _).
  - intros y A [x p]. apply (a x (p^ # A)).
  - intros x. apply path_forall. intros y. reflexivity.
Defined.

(** The above (co)unit constructions are special cases of the following, which tells us that these extensions are adjoint to restriction by [j] *)
Definition leftadjoint_leftkantypefamily `{Funext} {X Y : Type} (f : X -> Type)
  (g : Y -> Type) (j : X -> Y)
  : ((LeftKanTypeFamily f j) =< g) <~> (f =< g o j).
Proof.
  snrapply equiv_adjointify.
  - intros a x B. apply (a (j x) ((x; idpath); B)).
  - intros b y [[x p] C]. apply (p # (b x C)).
  - intros b. apply path_forall. intros x.
    apply path_forall. intros B; cbn. reflexivity.
  - intros a. apply path_forall. intros y.
    apply path_forall. intros [[x []] C]; cbn. reflexivity.
Defined.

Definition rightadjoint_rightkantypefamily `{Funext} {X Y : Type} (f : X -> Type)
  (g : Y -> Type) (j : X -> Y)
  : (g =< (RightKanTypeFamily f j)) <~> (g o j =< f).
Proof.
  snrapply equiv_adjointify.
  - intros a x C. apply (a (j x) C (x; idpath)).
  - intros a y C [x p]. apply (a x). apply (p^ # C).
  - intros a. apply path_forall. intros x. apply path_forall. intros C; cbn. reflexivity.
  - intros b. apply path_forall. intros y. apply path_forall. intros C.
    apply path_forall. intros [x p]. destruct p; cbn. reflexivity.
Defined.

(** This section is all set up for the proof that the left Kan extension of an embedding is an embedding of type families. *)
Section EmbedProofLeft.
  Context `{Univalence} {X Y : Type} (j : X -> Y) (isem : IsEmbedding j).

  Let s := (fun f => LeftKanTypeFamily f j).
  Let r := (fun g : Y -> Type => g o j).
  Let M := { g | forall y, IsEquiv (counit_leftkantypefam g j y) }.

  (** Helper functions for the proof of [isptwiseequiv_leftkancounit]. *)
  Local Definition t : forall (f : X -> Type) (x x' : X) (u : x' = x) (p : j x' = j x) (C : f x'), (ap j u = p)
                    -> ((x'; p); ((x'; idpath); C))
                    = (((x; idpath); ((x'; p); C)) : sig (fun '((x; _) : hfiber j (j x)) => r (s f) x)).
  Proof. intros f x0 x0' [] p C0 []; reflexivity. Defined.

  Let q : (forall x x' : X, IsEquiv (@ap X Y j x x'))
    := fun x x' : X => isequiv_ap_isembedding j x x'.
  Let pa : (forall x x' : X, (j x = j x') -> (x = x'))
    := fun x x' : X => (@equiv_inv _ _ _ (q x x')).
  Let appa : (forall x x' p', ap j (pa x' x p') = p')
    := fun x x' : X => (eisretr (@ap X Y j x' x)).

  Definition isptwiseequiv_leftkancounit : (X -> Type) -> M.
  Proof.
    intros f. srefine (s f; _). intros y.
    snrapply isequiv_adjointify.
    - apply (fun '(((x; p); C) : s f y) => ((x; p); ((x; idpath); C))).
    - intros [[x []] C]. reflexivity.
    - intros [[x []] [[x' p'] C]].
      apply (t f x x' (pa x' x p') p' C (appa x x' p')).
  Defined.

  Definition isequiv_isptwiseequiv_leftkancounit : IsEquiv isptwiseequiv_leftkancounit.
  Proof.
    snrapply isequiv_adjointify.
    - intros [g e]. apply (r g).
    - intros [g e]. srapply path_sigma.
      * apply path_forall. intros y. 
        apply (@path_universe_uncurried H (s (r g) y) (g y)).
        apply issig_equiv.
        apply (counit_leftkantypefam g j y; e y).
      * snrefine (path_ishprop _ _).
        refine istrunc_forall.
    - intros f. apply path_forall. intros x.
      apply (path_universe_uncurried (isext_leftkantypefamily _ _ _ _)).
  Defined.

  (** Using these facts we can show that the map [_ <| j] is an embedding if [j] is an embedding. *)
  Definition isembed_leftkantypefam_ext
    : IsEmbedding (fun f => LeftKanTypeFamily f j).
  Proof.
    snrapply (istruncmap_compose (-1) isptwiseequiv_leftkancounit (@pr1 (Y -> Type)
      (fun g => forall y, IsEquiv (counit_leftkantypefam g j y)))).
    - rapply istruncmap_mapinO_tr.
    - rapply istruncmap_mapinO_tr.
      rapply mapinO_isequiv.
      apply isequiv_isptwiseequiv_leftkancounit.
  Defined.

End EmbedProofLeft.

(** Dual proof for the right Kan extension. *)
Section EmbedProofRight.
  Context `{Univalence} {X Y : Type} (j : X -> Y) (isem : IsEmbedding j).

  Let s := (fun f => RightKanTypeFamily f j).
  Let r := (fun g : Y -> Type => g o j).
  Let M := {g | forall y, IsEquiv (unit_rightkantypefam g j y)}.

  Definition isptwiseequiv_rightkanunit : (X -> Type) -> M.
  Proof.
    intros f. srefine (s f; _). intros y.
    snrapply isequiv_adjointify.
    - intros C [x p]. apply (C (x; p) (x; idpath)).
    - intros C. apply path_forall. intros [x p]. destruct p.
      apply path_forall. intros w.
      rapply (@transport _ (fun t => C t (t.1; idpath) = C (x; idpath) t) _ w
        (center _ (isem (j x) (x; idpath) w)) idpath).
    - intros a. apply path_forall. intros [x p]. destruct p.
      reflexivity.
  Defined.
      
  Definition isequiv_isptwiseequiv_rightkanunit : IsEquiv isptwiseequiv_rightkanunit.
  Proof.
    snrapply isequiv_adjointify.
    - intros [g e]. apply (r g).
    - intros [g e]. srapply path_sigma.
      * apply path_forall. intros y.
        apply (@path_universe_uncurried H (s (r g) y) (g y)).
        symmetry. apply (Build_Equiv _ _ (unit_rightkantypefam g j y) (e y)).
      * snrefine (path_ishprop _ _).
        refine istrunc_forall.
    - intros f. apply path_forall. intros x.
      apply (path_universe_uncurried (isext_rightkantypefamily _ _ _ _)).
  Defined.

  (** The map [_ |> j] is an embedding if [j] is an embedding. *)
  Definition isembed_rightkantypefam_ext
    : IsEmbedding (fun f => RightKanTypeFamily f j).
  Proof.
    snrapply (istruncmap_compose (-1) isptwiseequiv_rightkanunit (@pr1 (Y -> Type)
      (fun g => forall y, IsEquiv (unit_rightkantypefam g j y)))).
    - rapply istruncmap_mapinO_tr.
    - rapply istruncmap_mapinO_tr.
      rapply mapinO_isequiv.
      apply isequiv_isptwiseequiv_rightkanunit.
  Defined.

End EmbedProofRight.
