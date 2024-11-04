(* -*- mode: coq; mode: visual-line -*-  *)
(** * Kan Extension of Type Families *)

(** * Part of Formalization of section 4 of the paper: Injective Types in Univalent Mathematics by Martin Escardo *)
(** Many proofs guided by Martin Escardo's original Agda formalization of this paper which can be found at: https://www.cs.bham.ac.uk/~mhe/TypeTopology/InjectiveTypes.Article.html *)

Require Import Basics.
Require Import Types.Sigma Types.Unit Types.Forall Types.Empty Types.Universe Types.Equiv.
Require Import HFiber.
Require Import Truncations.Core.
Require Import ReflectiveSubuniverse.


(** Being careful about universe structure for these first few definitions because they are used in the rest of the paper *)
Section UniverseStructure.
  Universe u v w uv uw vw uvw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
    uv <= uvw, uw <= uvw, vw <= uvw.

  Definition LeftKanTypeFamily@{} {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w}) (j : X -> Y)
    := (fun y => sig@{uv w} (fun w : (hfiber j y) => f (w.1))).

  Definition RightKanTypeFamily@{} {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w}) (j : X -> Y)
    := (fun y => forall w : (hfiber j y), f (w.1)).

  (*FIX*)
  Notation "f <| j" := (LeftKanTypeFamily f j) (at level 40).
  Notation "f |> j" := (RightKanTypeFamily f j) (at level 40).

  (** If [j] is an embedding, then [f <| j] and [f |> j] are extensions in the following sense: [(f <| j o j)x <~> fx <~> (f |> j o j)] *)
  Definition isext_leftkantypefamily@{} {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w}) (j : X -> Y)
    (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} ((LeftKanTypeFamily@{} f j) (j x)) (f x).
  Proof.
    transparent assert (C : (Contr (hfiber@{u v} j (j x)))).
    - srapply contr_inhabited_hprop@{uv}. exact (x; idpath (j x)).
    - snrapply (@equiv_contr_sigma@{uv w uvw} _ _ C).
  Defined.

  Definition isext_rightkantypefamily@{} `{Funext} {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w}) (j : X -> Y)
    (isem : IsEmbedding@{u v uv} j) (x : X)
    : Equiv@{uvw w} ((RightKanTypeFamily@{} f j) (j x)) (f x).
  Proof.
    transparent assert (C : (Contr (hfiber@{u v} j (j x)))).
    - srapply contr_inhabited_hprop@{uv}. exact (x; idpath (j x)).
    - snrapply (@equiv_contr_forall@{uv w uvw} _ _ C).
  Defined.

End UniverseStructure.

(*Move*)
Definition isempty_empty_indexed_sig (A : Type) (P : A -> Type) (na : A -> Empty)
  : { a | P a } <~> Empty := equiv_to_empty (fun ap => na ap.1).

Definition isunit_empty_indexed_forall `{Funext} (A : Type) (P : A -> Type) (na : A -> Empty)
  : (forall a, P a) <~> Unit.
Proof.
  snrapply equiv_contr_unit.
  snrapply contr_forall.
  apply (fun a => Empty_rec (na a)).
Defined.

(** For [y : Y] no in the image of [j], [(f <| j)y <~> Empty] and [(f |> j)y <~> Unit] *)
Definition isempty_leftkantypefamily {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w})
  (j : X -> Y) (y : Y) (ynin : forall x : X, j x = y -> Empty)
  : LeftKanTypeFamily f j y <~> Empty := isempty_empty_indexed_sig _ _ (fun w => ynin w.1 w.2).

Definition isunit_rightkantypefamily `{Funext} {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w})
  (j : X -> Y) (y : Y) (ynin : forall x : X, j x = y -> Empty)
  : RightKanTypeFamily f j y <~> Unit := isunit_empty_indexed_forall _ _ (fun w => ynin w.1 w.2).

Definition equiv_leftkantypefamily {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w}) (j : X -> Y)
  : (sig f) <~> sig (LeftKanTypeFamily f j).
Proof.
  snrapply equiv_adjointify.
  - apply (fun w : (sig f) => (j w.1; (w.1; idpath); w.2)).
  - apply (fun '((y; ((x; p); y')) : sig (LeftKanTypeFamily f j)) => (x; y')).
  - intros [y [[x []] y']]. reflexivity.
  - intros [x y]. reflexivity.
Defined.

Definition equiv_rightkantypefamily `{Funext} {X : Type@{u}} {Y : Type@{v}} (f : X -> Type@{w}) (j : X -> Y)
  : (forall x, f x) <~> (forall y, (RightKanTypeFamily f j) y).
Proof.
  snrapply equiv_adjointify.
  - intros g y w. apply (g w.1).
  - apply (fun h x => h (j x) (x; idpath)).
  - intros h. apply path_forall. intros y. apply path_forall.
    intros [x []]. reflexivity.
  - intros g. apply path_forall. intros y. reflexivity.
Defined.
(** Note that these equivalences tell us that [sig (f <| j)] and [forall (f |> j)] can be thought of as just different notation for the sum and product of a type family *)

(** Here we are taking the perspective of a type family [f : X -> Type] being a sort of oo-presheaf, considering the interpretation of [X] as an oo-ggroupoid and [Type] as a universe of spaces i.e. an appropriate generalization of the category of sets *)
(** It is easy to see that a type family [f] is functorial if we define its action on paths as follows *)
Definition path_action_type_family {X : Type} {x y : X} (f : X -> Type) (p : x = y) := transport f p.

(* FIX *)
Notation "f [ p ]" := (path_action_type_family f p) (at level 70).

Definition id_functoriality_type_family {X : Type} {x : X} (f : X -> Type)
  : path_action_type_family f (idpath x) = idmap := idpath.

Definition comp_functoriality_type_family {X : Type} {x y z : X} (f : X -> Type) (p : x = y) (q : y = z)
  : path_action_type_family f (p @ q) = (path_action_type_family f q) o (path_action_type_family f p).
Proof.
  destruct p, q. reflexivity.
Defined.

(** We can now define the type of transformations between two type families *)
Definition ooPresheafTransforms {X : Type@{u}} (f : X -> Type@{w}) (f' : X -> Type@{w'})
  := forall x, (f x) -> (f' x).

Notation "f =< g" := (ooPresheafTransforms f g) (at level 60).

(** It is again easy to see that these transformations are automatically natural by their definition *)
Definition naturality_oopresheaftransforms {X : Type} {x y : X} (f f' : X -> Type)
  (a : f =< f') (p : x = y)
  : (a y) o (path_action_type_family f p) = (path_action_type_family f' p) o (a x).
Proof.
  destruct p. reflexivity.
Defined.

Definition comp_transformation {X} {f g h : X -> Type} (b : g =< h) (a : f =< g)
  : f =< h := fun x A => (b x) (a x A).

Definition whisker_transformation {X Y} (j : X -> Y) {f g : Y -> Type} (a : f =< g)
  : f o j =< g o j := fun x A => (a (j x) A).

(** If [j] is an embedding then [(f <| j) =< (f |> j)] *)
Definition transform_leftkantypefam_rightkantypefam {X Y : Type} (f : X -> Type)
  (j : X -> Y) (isem : IsEmbedding j)
  : (LeftKanTypeFamily f j) =< (RightKanTypeFamily f j).
Proof.
  intros y [w' z] w.
  snrapply (transport (fun a => f a.1) _ z).
  srapply path_ishprop.
Defined.

(** Under this interpretation, we can think of the maps [f <| j] and [f |> j] as left and right Kan extentions of [f : X -> Type] along [j : X -> Y] *)
(** To see this we can construct the (co)unit transformations of our extensions *)
Definition unit_leftkantypefam {X Y : Type} (f : X -> Type) (j : X -> Y)
  : f =< (LeftKanTypeFamily f j o j) := (fun x A => ((x; idpath); A)).
  
Definition counit_rightkantypefam {X Y : Type} (f : X -> Type) (j : X -> Y)
  : (RightKanTypeFamily f j o j) =< f := (fun x A => A (x; idpath)).

(** Universal property of the Kan extensions *)
Definition univ_property_LeftKanTypeFam `{Funext} {X Y} {j : X -> Y} {f : X -> Type} {g : Y -> Type} (a : f =< g o j)
  : { b : LeftKanTypeFamily f j =< g | comp_transformation (whisker_transformation j b) (unit_leftkantypefam f j) == a}.
Proof.
  snrefine (_; _).
  - intros y [[x p] A]. apply (p # a x A).
  - intros x. apply path_forall. intros y. reflexivity.
Defined.

(*
Definition contr_univ_property_LeftKanTypeFam `{Funext} {X Y} {j : X -> Y} {f : X -> Type} {g : Y -> Type} {a : f =< g o j}
  : Contr { b : LeftKanTypeFamily f j =< g | comp_transformation (whisker_transformation j b) (unit_leftkantypefam f j) == a}.
Proof.
  apply (Build_Contr _ (univ_property_LeftKanTypeFam a)).
  intros [b F]. srapply path_sigma.
  - apply path_forall. intros y. apply path_forall. intros [[w []] c].
    srefine (ap10 (F w) c)^.
  - apply path_forall. intros x.
Admitted.
*)

(** The above (co)unit constructions are special cases of the following, which tells us that these extensions are adjoint to restriction by [j] *)
Definition leftadjoint_leftkantypefamily `{Funext} {X Y : Type} (f : X -> Type)
  (g : Y -> Type) (j : X -> Y)
  : ((LeftKanTypeFamily f j) =< g) <~> (f =< g o j).
Proof.
  snrapply equiv_adjointify.
  - intros a x B. apply (a (j x) ((x; idpath); B)).
  - intros b y [[x p] C]. apply (p # (b x C)).
  - intros b. apply path_forall. intros x. apply path_forall. intros B. reflexivity.
  - intros a. apply path_forall. intros y. apply path_forall. intros [[x []] C]. reflexivity.
Defined.

Definition rightadjoint_rightkantypefamily `{Funext} {X Y : Type} (f : X -> Type)
  (g : Y -> Type) (j : X -> Y)
  : (g =< (RightKanTypeFamily f j)) <~> (g o j =< f).
Proof.
  snrapply equiv_adjointify.
  - intros a x C. apply (a (j x) C (x; idpath)).
  - intros a y C [x p]. apply (a x). apply (p^ # C).
  - intros a. apply path_forall. intros x. apply path_forall. intros C. reflexivity.
  - intros b. apply path_forall. intros y. apply path_forall. intros C.
    apply path_forall. intros [x p]. destruct p. reflexivity.
Defined.

(** This section is all set up for the proof that the extension of an embedding is an embedding of type families *)
Section EmbedProofLeft.
  Context `{Univalence} {X Y : Type} (j : X -> Y) (isem : IsEmbedding j).

  Let s := (fun f => LeftKanTypeFamily f j).
  Let r := (fun g : Y -> Type => g o j).

  Local Definition k : forall g, s (r g) =< g.
    Proof. intros g y [[x p] C]; apply (transport g p C). Defined.
  
  Let M := { g | forall y, IsEquiv (k g y) }.

  Local Definition t : forall (f : X -> Type) (x x' : X) (u : x' = x) (p : j x' = j x) (C : f x'), (ap j u = p)
                    -> ((x'; p); ((x'; idpath); C))
                    = (((x; idpath); ((x'; p); C)) : sig (fun '((x; _) : hfiber j (j x)) => r (s f) x)).
  Proof. intros f x0 x0' [] p C0 []; reflexivity. Defined.

  Let q : (forall x x' : X, IsEquiv (@ap X Y j x x')) := fun x x' : X => isequiv_ap_isembedding j x x'.

  Let pa : (forall x x' : X, (j x = j x') -> (x = x'))
    := fun x x' : X => (@equiv_inv _ _ _ (q x x')).
  Let appa : (forall x x' p', ap j (pa x' x p') = p')
    := fun x x' : X => (eisretr (@ap X Y j x' x)).

  Local Definition F : (X -> Type) -> M.
  Proof.
    intros f. srefine (s f; _). intros y. snrapply isequiv_adjointify.
    - apply (fun '(((x; p); C) : s f y) => ((x; p); ((x; idpath); C))).
    - intros [[x []] C]. reflexivity.
    - intros [[x []] [[x' p'] C]]. apply (t f x x' (pa x' x p') p' C (appa x x' p')).
  Defined.

  Local Definition isequiv_F : IsEquiv F.
  Proof.
    snrapply isequiv_adjointify.
    - intros [g e]. apply (r g).
    - intros [g e]. srapply path_sigma.
      * apply path_forall. intros y. apply (@path_universe_uncurried H (s (r g) y) (g y)).
        apply issig_equiv. apply (k g y; e y).
      * snrefine (path_ishprop _ _). refine istrunc_forall.
    - intros f. apply path_forall. intros x.
      apply (path_universe_uncurried (isext_leftkantypefamily _ _ _ _)).
  Defined.

  (** Using these facts we can show that the map [_ <| j] is an embedding if [j] is an embedding *)
  Definition isembed_leftkantypefam_ext
    : IsEmbedding (fun f => LeftKanTypeFamily f j).
  Proof.
    snrapply (istruncmap_compose (-1) F (@pr1 (Y -> Type) (fun g => forall y, IsEquiv (k g y)))).
    - rapply istruncmap_mapinO_tr.
    - rapply istruncmap_mapinO_tr.
      rapply mapinO_isequiv.
      apply isequiv_F.
  Defined.

End EmbedProofLeft.

(** Dual proof for the right Kan extension*)
Section EmbedProofRight.
  Context `{Univalence} {X Y : Type} (j : X -> Y) (isem : IsEmbedding j).

  Let s := (fun f => RightKanTypeFamily f j).
  Let r := (fun g : Y -> Type => g o j).

  (*
  Definition isembed_rightkantypefam_ext
    : IsEmbedding (fun f => RightKanTypeFamily f j).
  Proof.
  Admitted.
  *)

End EmbedProofRight.