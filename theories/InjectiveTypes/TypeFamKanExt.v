(** * Kan extensions of type families *)

(** This is part of the formalization of section 4 of the paper: Injective Types in Univalent Mathematics by Martin Escardo.  Many proofs are guided by Martin Escardo's original Agda formalization of this paper which can be found at: https://www.cs.bham.ac.uk/~mhe/TypeTopology/InjectiveTypes.Article.html. *)

Require Import Basics.
Require Import Types.Sigma Types.Unit Types.Forall Types.Empty Types.Universe Types.Equiv Types.Paths.
Require Import HFiber.
Require Import Truncations.Core.
Require Import ReflectiveSubuniverse Modality.

(** We are careful about universe variables for these first few definitions because they are used in the rest of the paper.  We use [u], [v], [w], etc. as our typical universe variables. Our convention for the max of two universes [u] and [v] is [uv]. *)

Section UniverseStructure.
  Universes u v w uv uw vw uvw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
    uv <= uvw, uw <= uvw, vw <= uvw.

  Definition LeftKanFam@{} {X : Type@{u}} {Y : Type@{v}} (P : X -> Type@{w}) (j : X -> Y)
    : Y -> Type@{uvw}
    := fun y => sig@{uv w} (fun (w : hfiber j y) => P (w.1)).

  Definition RightKanFam@{} {X : Type@{u}} {Y : Type@{v}} (P : X -> Type@{w}) (j : X -> Y)
    : Y -> Type@{uvw}
    := fun y => forall (w : hfiber j y), P (w.1).

  (** Below we will introduce notations [P <| j] and [P |> j] for these Kan extensions. *)

  (* If [j] is an embedding, then [P <| j] and [P |> j] are extensions in the following sense: [(P <| j o j) x <~> P x <~> (P |> j o j) x].  So, with univalence, we get that they are extensions. *)

  Definition isext_leftkanfam@{} {X : Type@{u}} {Y : Type@{v}}
    (P : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} (LeftKanFam@{} P j (j x)) (P x).
  Proof.
    rapply (@equiv_contr_sigma (hfiber j (j x)) _ _).
  Defined.

  Definition isext_rightkanfam@{} `{Funext} {X : Type@{u}} {Y : Type@{v}}
    (P : X -> Type@{w}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} (RightKanFam@{} P j (j x)) (P x).
  Proof.
    rapply (@equiv_contr_forall _ (hfiber j (j x)) _ _).
  Defined.

End UniverseStructure.

Notation "P <| j" := (LeftKanFam P j) : function_scope.
Notation "P |> j" := (RightKanFam P j) : function_scope.

(** For [y : Y] not in the image of [j], [(P <| j) y] is empty and [(P |> j) y] is contractible. *)
Definition isempty_leftkanfam {X : Type} {Y : Type}
  (P : X -> Type) (j : X -> Y) (y : Y) (ynin : forall x : X, j x <> y)
  : (P <| j) y -> Empty
  := fun '((x; p); _) => ynin x p.

Definition contr_rightkanfam `{Funext} {X : Type} {Y : Type}
  (P : X -> Type@{w}) (j : X -> Y) (y : Y) (ynin : forall x : X, j x <> y)
  : Contr ((P |> j) y).
Proof.
  snrapply contr_forall.
  intros [x p].
  apply (Empty_rec (ynin x p)).
Defined.

(** The following equivalences tell us that [{ y : Y & (P <| j) y}] and [forall y : Y, (P |> j) y] can be thought of as just different notation for the sum and product of a type family. *)
Definition equiv_leftkanfam {X : Type} {Y : Type}
  (P : X -> Type) (j : X -> Y)
  : {x : X & P x} <~> {y : Y & (P <| j) y}.
Proof.
  snrapply equiv_adjointify.
  - apply (fun w : {x : X & P x} => (j w.1; (w.1; idpath); w.2)).
  - apply (fun '((y; ((x; p); y')) : {y : Y & (P <| j) y}) => (x; y')).
  - intros [y [[x []] y']]; cbn. reflexivity.
  - intros [x y]; cbn. reflexivity.
Defined.

Definition equiv_rightkanfam `{Funext} {X : Type} {Y : Type}
  (P : X -> Type@{w}) (j : X -> Y)
  : (forall x, P x) <~> (forall y, (P |> j) y).
Proof.
  snrapply equiv_adjointify.
  - intros g y w. apply (g w.1).
  - apply (fun h x => h (j x) (x; idpath)).
  - intros h. funext y. funext [x []]; cbn. reflexivity.
  - intros g. apply path_forall. reflexivity.
Defined.

(** Here we are taking the perspective that a type family [P : X -> Type] is a sort of oo-presheaf, considering the interpretation of [X] as an oo-groupoid and [Type] as a universe of spaces i.e. an appropriate generalization of the category of sets. It is easy to see that a type family [P] is functorial if we define its action on paths with [transport]. Functoriality then reduces to known lemmas about the [transport] function. *)

(** With this in mind, we define the type of transformations between two type families. *)
Definition MapFam {X : Type} (P : X -> Type) (R : X -> Type)
  := forall x, P x -> R x.

Notation "P >=> R" := (MapFam P R) : function_scope.

(** [concat_Ap] says that these transformations are automatically natural. *)

(** Composition of transformations. *)
Definition compose_mapfam {X} {P R Q : X -> Type} (b : R >=> Q) (a : P >=> R)
  : P >=> Q
  := fun x => (b x) o (a x).

(** If [j] is an embedding then [(P <| j) =< (P |> j)]. *)
Definition transform_leftkanfam_rightkanfam {X Y : Type}
  (P : X -> Type) (j : X -> Y) (isem : IsEmbedding j)
  : (P <| j) >=> (P |> j).
Proof.
  intros y [w' z] w.
  snrapply (transport (fun a => P a.1) _ z).
  srapply path_ishprop.
Defined.

(** Under this interpretation, we can think of the maps [P <| j] and [P |> j] as left and right Kan extensions of [P : X -> Type] along [j : X -> Y]. To see this we can construct the (co)unit transformations of our extensions. *)
Definition unit_leftkanfam {X Y : Type} (P : X -> Type) (j : X -> Y)
  : P >=> ((P <| j) o j)
  := fun x A => ((x; idpath); A).
  
Definition counit_rightkanfam {X Y : Type} (P : X -> Type) (j : X -> Y)
  : ((P |> j) o j) >=> P
  := fun x A => A (x; idpath).

Definition counit_leftkanfam {X Y : Type} (R : Y -> Type) (j : X -> Y)
  : ((R o j) <| j) >=> R.
Proof.
  intros y [[x p] C].
  apply (transport R p C).
Defined.

Definition unit_rightkanfam {X Y : Type} (R : Y -> Type) (j : X -> Y)
  : R >=> ((R o j) |> j).
Proof.
  intros y C [x p].
  apply (transport R p^ C).
Defined.

(** Universal property of the Kan extensions. *)
Definition univ_property_leftkanfam {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} (a : P >=> R o j)
  : { b : P <| j >=> R & compose_mapfam (b o j) (unit_leftkanfam P j) == a}.
Proof.
  snrefine (_; _).
  - intros y [[x p] A]. apply (p # a x A).
  - intros x. reflexivity.
Defined.

Definition ap_path_forall_helper `{Funext} {A B : Type} (P : A -> Type) (Q : A -> Type)
  {f g : forall a, Q a -> P a} (h : f == g) (a : A) (i : B -> Q a)
  : ap (fun (k : forall a, Q a -> P a) => (fun b => k a (i b))) (path_forall _ _ h)
    = path_forall _ _ (fun b => ap10 (h a) (i b)).
Proof.
  revert h; rapply (equiv_ind apD10).
  intros []; cbn.
  unfold path_forall.
  rewrite (eissect apD10); cbn.
  symmetry; apply path_forall_1.
Defined.

Definition contr_univ_property_leftkanfam `{Funext} {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} {a : P >=> R o j}
  : Contr { b : P <| j >=> R | compose_mapfam (b o j) (unit_leftkanfam P j) == a}.
Proof.
  apply (Build_Contr _ (univ_property_leftkanfam a)).
  intros [b F].
  symmetry. (* Do now to avoid inversion in the first subgoal. *)
  srapply path_sigma.
  - funext y. funext [[w []] c]. srefine (ap10 (F w) c).
  - simpl.
    funext x.
    lhs nrapply transport_forall_constant.
    lhs nrapply transport_paths_Fl.
    apply moveR_Vp.
    rhs nrapply concat_p1.
    unfold compose_mapfam, unit_leftkanfam.
    rhs nrapply (ap_path_forall_helper _ _ _ (j x)).
    unfold path_forall, ap10.
    rewrite (eisretr apD10).
    symmetry; apply eissect.
Defined.

Definition univ_property_rightkanfam {X Y} {j : X -> Y}
  {P : X -> Type} {R : Y -> Type} (a : R o j >=> P)
  : { b : R >=> P |> j & compose_mapfam (counit_rightkanfam P j) (b o j) == a}.
Proof.
  snrefine (_; _).
  - intros y A [x p]. apply (a x (p^ # A)).
  - intros x. reflexivity.
Defined.

(** The above (co)unit constructions are special cases of the following, which tells us that these extensions are adjoint to restriction by [j] *)
Definition leftadjoint_leftkanfam `{Funext} {X Y : Type} (P : X -> Type)
  (R : Y -> Type) (j : X -> Y)
  : ((P <| j) >=> R) <~> (P >=> R o j).
Proof.
  snrapply equiv_adjointify.
  - intros a x B. apply (a (j x) ((x; idpath); B)).
  - intros b y [[x p] C]. apply (p # (b x C)).
  - intros b. funext x.
    funext B; cbn. reflexivity.
  - intros a. funext y.
    funext [[x []] C]; cbn. reflexivity.
Defined.

Definition rightadjoint_rightkanfam `{Funext} {X Y : Type} (P : X -> Type)
  (R : Y -> Type) (j : X -> Y)
  : (R >=> (P |> j)) <~> (R o j >=> P).
Proof.
  snrapply equiv_adjointify.
  - intros a x C. apply (a (j x) C (x; idpath)).
  - intros a y C [x p]. apply (a x). apply (p^ # C).
  - intros a. funext x. funext C; cbn. reflexivity.
  - intros b. funext y. funext C.
    funext [x p]. destruct p; cbn. reflexivity.
Defined.

(** This section is all set up for the proof that the left Kan extension of an embedding is an embedding of type families. *)
Section EmbedProofLeft.
  Context `{Univalence} {X Y : Type} (j : X -> Y) (isem : IsEmbedding j).

  (** Given a type family over [X] and an embedding [j : X -> Y], we can construct a type family over [Y] such that evey map in [counit_leftkanfam R j] is an equivalence i.e. the counit transformation is a natural isomorphism. *)
  Definition leftkanfam_counit_equiv (P : X -> Type)
    : { R : Y -> Type & forall y, IsEquiv (counit_leftkanfam R j y) }.
  Proof.
    srefine (P <| j; _). intros y.
    snrapply isequiv_adjointify.
    - apply (fun '(((x; p); C) : (P <| j) y) => ((x; p); ((x; idpath); C))).
    - cbn. intros [[x []] C]. reflexivity.
    - intros [[x []] [[x' p'] C]]; cbn; cbn in C, p'.
      revert p'; apply (equiv_ind (ap j)).
      by intros [].
  Defined.

  Global Instance isequiv_leftkanfam_counit_equiv : IsEquiv leftkanfam_counit_equiv.
  Proof.
    snrapply isequiv_adjointify.
    - intros [R e]. exact (R o j).
    - intros [R e]. srapply path_sigma_hprop; cbn.
      funext y.
      exact (path_universe _ (feq:=e y)).
    - intros P.
      funext x.
      exact (path_universe_uncurried (isext_leftkanfam _ _ _ _)).
  Defined.

  (** Using these facts we can show that the map [_ <| j] is an embedding if [j] is an embedding. *)
  Definition isembed_leftkanfam_ext
    : IsEmbedding (fun P => P <| j)
    := mapinO_compose (O:=-1) leftkanfam_counit_equiv pr1.

End EmbedProofLeft.

(** Dual proof for the right Kan extension. *)
Section EmbedProofRight.
  Context `{Univalence} {X Y : Type} (j : X -> Y) (isem : IsEmbedding j).

  Definition rightkanfam_unit_equiv (P : X -> Type)
    : {R : Y -> Type & forall y, IsEquiv (unit_rightkanfam R j y)}.
  Proof.
    srefine (P |> j; _). intros y.
    snrapply isequiv_adjointify.
    - intros C [x p]. apply (C (x; p) (x; idpath)).
    - intros C. funext [x p]. destruct p. funext w.
      rapply (@transport _ (fun t => C t (t.1; idpath) = C (x; idpath) t) _ w
        (center _ (isem (j x) (x; idpath) w)) idpath).
    - intros a. funext [x p]. destruct p.
      reflexivity.
  Defined.
      
  Global Instance isequiv_rightkanfam_unit_equiv : IsEquiv rightkanfam_unit_equiv.
  Proof.
    snrapply isequiv_adjointify.
    - intros [R e]. apply (R o j).
    - intros [R e]. srapply path_sigma_hprop; cbn.
      funext y.
      symmetry; exact (path_universe _ (feq:=e y)).
    - intros P.
      funext x.
      apply (path_universe_uncurried (isext_rightkanfam _ _ _ _)).
  Defined.

  (** The map [_ |> j] is an embedding if [j] is an embedding. *)
  Definition isembed_rightkanfam_ext
    : IsEmbedding (fun P => P |> j)
    := mapinO_compose (O:=-1) rightkanfam_unit_equiv pr1.

End EmbedProofRight.