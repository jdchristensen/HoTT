(** * Kan extensions of type families *)

(** This is part of the formalization of section 4 of the paper: Injective Types in Univalent Mathematics by Martin Escardo.  Many proofs are guided by Martin Escardo's original Agda formalization of this paper which can be found at: https://www.cs.bham.ac.uk/~mhe/TypeTopology/InjectiveTypes.Article.html. *)

Require Import Basics.
Require Import Types.Sigma Types.Unit Types.Forall Types.Empty Types.Universe Types.Equiv.
Require Import HFiber.
Require Import Truncations.Core.
Require Import ReflectiveSubuniverse.

(** We are careful about universe variables for these first few definitions because they are used in the rest of the paper.  We use [u], [v], [w], etc. as our typical universe variables. Our convention for the max of two universes [u] and [v] is [uv]. *)

Section UniverseStructure.
  Universes u v w uv uw vw uvw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
    uv <= uvw, uw <= uvw, vw <= uvw.

  Definition LeftKanTypeFamily@{} {X : Type@{u}} {Y : Type@{v}} (P : X -> Type@{w}) (j : X -> Y)
    : Y -> Type@{uvw}
    := fun y => sig@{uv w} (fun (w : hfiber j y) => P (w.1)).

  Definition RightKanTypeFamily@{} {X : Type@{u}} {Y : Type@{v}} (P : X -> Type@{w}) (j : X -> Y)
    : Y -> Type@{uvw}
    := fun y => forall (w : hfiber j y), P (w.1).

  (** Below we will introduce notations [P <| j] and [P |> j] for these Kan extensions. *)

  (* If [j] is an embedding, then [P <| j] and [P |> j] are extensions in the following sense: [(P <| j o j) x <~> P x <~> (P |> j o j) x].  So, with univalence, we get that they are extensions. *)

  Definition isext_leftkantypefamily@{} {X : Type@{u}} {Y : Type@{v}}
    (P : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} (LeftKanTypeFamily@{} P j (j x)) (P x).
  Proof.
    transparent assert (C : (Contr (hfiber j (j x)))).
    - srapply contr_inhabited_hprop. exact (x; idpath (j x)).
    - snrapply (@equiv_contr_sigma _ _ C).
  Defined.

  Definition isext_rightkantypefamily@{} `{Funext} {X : Type@{u}} {Y : Type@{v}}
    (P : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} (RightKanTypeFamily@{} P j (j x)) (P x).
  Proof.
    transparent assert (C : (Contr (hfiber j (j x)))).
    - srapply contr_inhabited_hprop. exact (x; idpath (j x)).
    - snrapply (@equiv_contr_forall _ _ C).
  Defined.

End UniverseStructure.

Notation "P <| j" := (LeftKanTypeFamily P j) (at level 40).
Notation "P |> j" := (RightKanTypeFamily P j) (at level 40).

(** For [y : Y] not in the image of [j], [(P <| j) y] is empty and [(P |> j) y] is contractible. *)
Definition isempty_leftkantypefamily {X : Type} {Y : Type}
  (P : X -> Type) (j : X -> Y) (y : Y) (ynin : forall x : X, j x <> y)
  : (P <| j) y -> Empty
  := fun '((x; p); _) => ynin x p.

Definition contr_rightkantypefamily `{Funext} {X : Type} {Y : Type}
  (P : X -> Type@{w}) (j : X -> Y) (y : Y) (ynin : forall x : X, j x <> y)
  : Contr ((P |> j) y).
Proof.
  snrapply contr_forall.
  intros [x p].
  apply (Empty_rec (ynin x p)).
Defined.

(** The following equivalences tell us that [{ y : Y & (P <| j) y}] and [forall y : Y, (P |> j) y] can be thought of as just different notation for the sum and product of a type family. *)
Definition equiv_leftkantypefamily {X : Type} {Y : Type}
  (P : X -> Type) (j : X -> Y)
  : {x : X & P x} <~> {y : Y & (P <| j) y}.
Proof.
  snrapply equiv_adjointify.
  - apply (fun w : {x : X & P x} => (j w.1; (w.1; idpath); w.2)).
  - apply (fun '((y; ((x; p); y')) : {y : Y & (P <| j) y}) => (x; y')).
  - intros [y [[x []] y']]; cbn. reflexivity.
  - intros [x y]; cbn. reflexivity.
Defined.

Definition equiv_rightkantypefamily `{Funext} {X : Type} {Y : Type}
  (P : X -> Type@{w}) (j : X -> Y)
  : (forall x, P x) <~> (forall y, (P |> j) y).
Proof.
  snrapply equiv_adjointify.
  - intros g y w. apply (g w.1).
  - apply (fun h x => h (j x) (x; idpath)).
  - intros h. apply path_forall. intros y. apply path_forall.
    intros [x []]; cbn. reflexivity.
  - intros g. apply path_forall. reflexivity.
Defined.

(** Here we are taking the perspective that a type family [P : X -> Type] is a sort of oo-presheaf, considering the interpretation of [X] as an oo-groupoid and [Type] as a universe of spaces i.e. an appropriate generalization of the category of sets. It is easy to see that a type family [P] is functorial if we define its action on paths with [transport]. Functoriality then reduces to known lemmas about the [transport] function. *)

(** With this in mind, we define the type of transformations between two type families. *)
Definition MapFamily {X : Type} (P : X -> Type) (R : X -> Type)
  := forall x, P x -> R x.

Notation "P ==> R" := (MapFamily P R) (at level 60).

(** [concat_Ap] says that these transformations are automatically natural. *)

(** Composition of transformations. *)
Definition compose_mapfamily {X} {P R Q : X -> Type} (b : R ==> Q) (a : P ==> R)
  : P ==> Q
  := fun x => (b x) o (a x).

(** If [j] is an embedding then [(P <| j) =< (P |> j)]. *)
Definition transform_leftkantypefam_rightkantypefam {X Y : Type}
  (P : X -> Type) (j : X -> Y) (isem : IsEmbedding j)
  : (P <| j) ==> (P |> j).
Proof.
  intros y [w' z] w.
  snrapply (transport (fun a => P a.1) _ z).
  srapply path_ishprop.
Defined.

(** Under this interpretation, we can think of the maps [P <| j] and [P |> j] as left and right Kan extensions of [P : X -> Type] along [j : X -> Y]. To see this we can construct the (co)unit transformations of our extensions. *)
Definition unit_leftkantypefam {X Y : Type} (P : X -> Type) (j : X -> Y)
  : P ==> ((P <| j) o j)
  := fun x A => ((x; idpath); A).
  
Definition counit_rightkantypefam {X Y : Type} (P : X -> Type) (j : X -> Y)
  : ((P |> j) o j) ==> P
  := fun x A => A (x; idpath).

Definition counit_leftkantypefam {X Y : Type} (R : Y -> Type) (j : X -> Y)
  : ((R o j) <| j) ==> R.
Proof.
  intros y [[x p] C].
  apply (transport R p C).
Defined.

Definition unit_rightkantypefam {X Y : Type} (R : Y -> Type) (j : X -> Y)
  : R ==> ((R o j) |> j).
Proof.
  intros y C [x p].
  apply (transport R p^ C).
Defined.

(** Universal property of the Kan extensions. *)
Definition univ_property_LeftKanTypeFam `{Funext} {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} (a : P ==> R o j)
  : { b : P <| j ==> R & compose_mapfamily (b o j) (unit_leftkantypefam P j) == a}.
Proof.
  snrefine (_; _).
  - intros y [[x p] A]. apply (p # a x A).
  - intros x. apply path_forall. intros y. reflexivity.
Defined.

(** TODO: Prove uniqueness of the universal property. *)
(*Definition contr_univ_property_LeftKanTypeFam `{Funext} {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} {a : P =< R o j}
  : Contr { b : LeftKanTypeFamily P j =< R | compose_mapfamily (b o j) (unit_leftkantypefam P j) == a}.
Proof.
  apply (Build_Contr _ (univ_property_LeftKanTypeFam a)).
  intros [b F]. srapply path_sigma.
  - apply path_forall. intros y. apply path_forall.
    intros [[w []] c]. srefine (ap10 (F w) c)^.
  - apply path_forall. intros x.
Abort.*)

Definition univ_property_RightKanTypeFam `{Funext} {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} (a : R o j ==> P)
  : { b : R ==> P |> j & compose_mapfamily (counit_rightkantypefam P j) (b o j) == a}.
Proof.
  snrefine (_; _).
  - intros y A [x p]. apply (a x (p^ # A)).
  - intros x. apply path_forall. intros y. reflexivity.
Defined.

(** The above (co)unit constructions are special cases of the following, which tells us that these extensions are adjoint to restriction by [j] *)
Definition leftadjoint_leftkantypefamily `{Funext} {X Y : Type} (P : X -> Type)
  (R : Y -> Type) (j : X -> Y)
  : ((P <| j) ==> R) <~> (P ==> R o j).
Proof.
  snrapply equiv_adjointify.
  - intros a x B. apply (a (j x) ((x; idpath); B)).
  - intros b y [[x p] C]. apply (p # (b x C)).
  - intros b. apply path_forall. intros x.
    apply path_forall. intros B; cbn. reflexivity.
  - intros a. apply path_forall. intros y.
    apply path_forall. intros [[x []] C]; cbn. reflexivity.
Defined.

Definition rightadjoint_rightkantypefamily `{Funext} {X Y : Type} (P : X -> Type)
  (R : Y -> Type) (j : X -> Y)
  : (R ==> (P |> j)) <~> (R o j ==> P).
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

  (** Given a type family over [X] and an embedding [j : X -> Y], we can construct a type family over [Y] such that evey map in [counit_leftkantypefam R j] is an equivalence i.e. the counit transformation is a natural isomorphism. *)
  Definition isptwiseequiv_leftkancounit (P : X -> Type)
    : { R : Y -> Type & forall y, IsEquiv (counit_leftkantypefam R j y) }.
  Proof.
    srefine (P <| j; _). intros y.
    snrapply isequiv_adjointify.
    - apply (fun '(((x; p); C) : (P <| j) y) => ((x; p); ((x; idpath); C))).
    - intros [[x []] C]. reflexivity.
    - intros [[x []] [[x' p'] C]]; cbn; cbn in C, p'.
      revert p'; apply (equiv_ind (ap j)).
      by intros [].
  Defined.

  Definition isequiv_isptwiseequiv_leftkancounit : IsEquiv isptwiseequiv_leftkancounit.
  Proof.
    snrapply isequiv_adjointify.
    - intros [R e]. apply (R o j).
    - intros [R e]. srapply path_sigma.
      * apply path_forall. intros y. 
        apply (@path_universe_uncurried H (((R o j) <| j) y) (R y)).
        apply issig_equiv.
        apply (counit_leftkantypefam R j y; e y).
      * snrefine (path_ishprop _ _).
        refine istrunc_forall.
    - intros P. apply path_forall. intros x.
      apply (path_universe_uncurried (isext_leftkantypefamily _ _ _ _)).
  Defined.

  (** Using these facts we can show that the map [_ <| j] is an embedding if [j] is an embedding. *)
  Definition isembed_leftkantypefam_ext
    : IsEmbedding (fun P => P <| j).
  Proof.
    snrapply (istruncmap_compose (-1) isptwiseequiv_leftkancounit (@pr1 (Y -> Type)
      (fun R => forall y, IsEquiv (counit_leftkantypefam R j y)))).
    - rapply istruncmap_mapinO_tr.
    - rapply istruncmap_mapinO_tr.
      rapply mapinO_isequiv.
      apply isequiv_isptwiseequiv_leftkancounit.
  Defined.

End EmbedProofLeft.

(** Dual proof for the right Kan extension. *)
Section EmbedProofRight.
  Context `{Univalence} {X Y : Type} (j : X -> Y) (isem : IsEmbedding j).

  Definition isptwiseequiv_rightkanunit (P : X -> Type)
    : {R :Y -> Type & forall y, IsEquiv (unit_rightkantypefam R j y)}.
  Proof.
    srefine (P |> j; _). intros y.
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
    - intros [R e]. apply (R o j).
    - intros [R e]. srapply path_sigma.
      * apply path_forall. intros y.
        apply (@path_universe_uncurried H (((R o j) |> j) y) (R y)).
        symmetry. apply (Build_Equiv _ _ (unit_rightkantypefam R j y) (e y)).
      * snrefine (path_ishprop _ _).
        refine istrunc_forall.
    - intros P. apply path_forall. intros x.
      apply (path_universe_uncurried (isext_rightkantypefamily _ _ _ _)).
  Defined.

  (** The map [_ |> j] is an embedding if [j] is an embedding. *)
  Definition isembed_rightkantypefam_ext
    : IsEmbedding (fun P => P |> j).
  Proof.
    snrapply (istruncmap_compose (-1) isptwiseequiv_rightkanunit (@pr1 (Y -> Type)
      (fun R => forall y, IsEquiv (unit_rightkantypefam R j y)))).
    - rapply istruncmap_mapinO_tr.
    - rapply istruncmap_mapinO_tr.
      rapply mapinO_isequiv.
      apply isequiv_isptwiseequiv_rightkanunit.
  Defined.

End EmbedProofRight.
