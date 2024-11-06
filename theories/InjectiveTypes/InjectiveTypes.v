(** * Injective Types *)

(** ** Formalization of the paper: Injective Types in Univalent Mathematics by Martin Escardo. *)

(* MAKE NOTE OF CONVENTIONS FOR UNIVERSE NOTATION IN COMMENTS - also check spelling *)

Require Import Basics.
Require Import PropResizing.
Require Import Truncations.
Require Import Types.Universe Types.Unit.
Require Import HFiber.
Require Import HProp.
Require Import PropResizing.

Require Import YonedaPaths.
Require Import TypeFamKanExt.

Unset Printing Universes.

Section UniverseStructure.
  Universes u v w uv uw vw uvw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
    uv <= uvw, uw <= uvw, vw <= uvw.

  Definition IsInjectiveType@{} (D : Type@{w})
    := forall (X : Type@{u}) (Y : Type@{v}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j)
      (f : X -> D), merely@{uvw} (sig@{vw uw} (fun f' => f' o j == f)).

  Definition IsAlgebraicInjectiveType@{} (D : Type@{w})
    := forall (X : Type@{u}) (Y : Type@{v}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j)
      (f : X -> D), sig@{vw uw} (fun f' => f' o j == f).

  (** Contractible types are algebraically injective. *)
  Definition is_alginj_contr@{} (D : Type@{w}) (cD : Contr D)
    : IsAlgebraicInjectiveType@{} D.
  Proof.
    intros X Y j isem f.
    srefine (const (center D); _).
    intros x.
    apply (contr _).
  Defined.

End UniverseStructure.

(** [Type@{uv}] is algebraically u,v-injective in at least two ways *)
Definition alg_inj_Type@{u v suv uv | u <= uv, v <= uv, uv < suv} `{Univalence}
  : IsAlgebraicInjectiveType@{u v suv uv suv suv suv} Type@{uv}.
Proof.
  intros X Y j isem f.
  snrefine (_; _).
  - exact (LeftKanTypeFamily f j).
  - intros x. apply (path_universe_uncurried (isext_leftkantypefamily _ _ isem _)).
Defined.

Definition alg_inj_Type'@{u v suv uv | u <= uv, v <= uv, uv < suv} `{Univalence}
  : IsAlgebraicInjectiveType@{u v suv uv suv suv suv} Type@{uv}.
Proof.
  intros X Y j isem f.
  snrefine (_; _).
  - exact (RightKanTypeFamily f j).
  - intros x. apply (path_universe_uncurried (isext_rightkantypefamily _ _ isem _)).
Defined.


(** ** Constructions with algebraically injective types. *)


(** Retracts of algebraically injective types are algebraically injective. *)
Definition alg_inj_retract@{u v w w' uv uw vw uw' vw' uvw uvw' | u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw, uv <= uvw, uw <= uvw, vw <= uvw,
                              u <= uw', v <= vw', w' <= uw', w' <= vw', uv <= uvw', uw' <= uvw', vw' <= uvw'}
  {D' : Type@{w'}} {D : Type@{w}} (r : D -> D') {s : D' -> D}
  (retr : r o s == idmap) (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw uvw} D)
  : IsAlgebraicInjectiveType@{u v w' uv uw' vw' uvw'} D'.
Proof.
  intros X Y j isem f.
  snrefine (_; _).
  - exact (r o (Dai _ _ _ _ (s o f)).1).
  - intros x. rhs_V apply (retr (f x)).
    apply (ap r ((Dai _ _ _ _ (s o f)).2 x)).
Defined.
  
(** Dependent products are algebraically injective when all their factors are. *)
Definition alg_inj_forall@{u v w t uv uw vw tw uvw utw vtw utvw | u <= uv, u <= uw, v <= vw, v <= uv, w <= uw, w <= vw, w <= tw, t <= tw,
                           uv <= uvw, uw <= uvw, uw <= utw, vw <= uvw, vw <= vtw, tw <= utw, tw <= vtw, uvw <= utvw, utw <= utvw, vtw <= utvw}
  `{Funext} {A : Type@{t}} (D : A -> Type@{w})
  (Dai : forall a, IsAlgebraicInjectiveType@{u v w uv uw vw uvw} (D a))
  : IsAlgebraicInjectiveType@{u v tw uv utw vtw utvw} (forall a, D a).
Proof.
  intros X Y j isem f.
  snrefine (_; _). 
  - exact (fun y a => (Dai a _ _ _ _ (fun x => f x a)).1 y).
  - intros x. apply path_forall. intros a.
    exact ((Dai a _ _ _ _ (fun x => f x a)).2 x).
Defined.

Definition alg_inj_arrow@{u v w t uv uw vw tw uvw utw vtw utvw | u <= uv, u <= uw, v <= vw, v <= uv, w <= uw, w <= vw, w <= tw, t <= tw,
                               uv <= uvw, uw <= uvw, uw <= utw, vw <= uvw, vw <= vtw, tw <= utw, tw <= vtw, uvw <= utvw, utw <= utvw, vtw <= utvw}
  `{Funext} {A : Type@{t}} {D : Type@{w}}
  (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw uvw} D)
  : IsAlgebraicInjectiveType@{u v tw uv utw vtw utvw} (A -> D).
Proof.
  apply (alg_inj_forall _).
  intros a.
  apply Dai.
Defined.

(** Algebraically injective types are retracts of any type that they embed into. *)
Definition retract_alg_inj_embedding@{v w vw | v <= vw, w <= vw}
  (D : Type@{w}) {Y : Type@{v}} (j : D -> Y) (isem : IsEmbedding j)
  (Dai : IsAlgebraicInjectiveType@{w v w vw w vw vw} D)
  : { r | r o j == idmap }
  := Dai _ _ _ _ idmap.

(** Any algebraically u,u^+-injective type [X : Type@{u}], is a retract of [X -> Type@{u}]. *)
Definition retract_power_universe_alg_usuinj@{u su | u < su} `{Univalence}
  (D : Type@{u}) (Dai : IsAlgebraicInjectiveType@{u su u su u su su} D)
  : { r : (D -> Type@{u}) -> D | r o (@paths D) == idmap }
  := retract_alg_inj_embedding D (@paths D) isembedding_paths Dai.

(** ** Algebraic flabbiness and resizing constructions. *)

(** If [D : Type@{u}] is algebraically u,u^+-injective, then it is algebraically u,u-injective. *)
(** Note that this proof is made trivial by the library's handeling of universes. *)
Definition alg_uuinj_alg_usu_inj@{u su | u < su} (D : Type@{u}) (Dai : IsAlgebraicInjectiveType@{u su u su u su su} D)
  : IsAlgebraicInjectiveType@{u u u u u u u} D := Dai.

Definition IsAlgebraicallyFlabbyType@{u w uw | u <= uw, w <= uw} (D : Type@{w})
  := forall (P : Type@{u}) (PropP : IsHProp P) (f : P -> D),
    { d : D | forall p : P, d = f p}.
(** We can think of algebraic flabbiness as algebraic injectivity, but only ranging over embeddings of propositions into the unit type. *)

(** Algebraically u,v-injective types are algebraically uv-flabby. *)
Definition alg_flab_alg_inj@{u v w uv uw vw uvw | u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw, uv <= uvw, uw <= uvw, vw <= uvw}
  {D : Type@{w}} (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw uvw} D)
  : IsAlgebraicallyFlabbyType@{u w uw} D.
Proof.
  intros P PropP f.
  snrefine (_; _).
  - srapply ((Dai _ _ (const_tt P) _ f).1 tt).
  - intros p. apply (Dai _ _ (const_tt P) _ f).2.
Defined.

(** Algebraically u-flabby types are algebraically u,v-injective. *)
Definition alg_inj_alg_flab@{u v w uv uw vw uvw | u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw, uv <= uvw, uw <= uvw, vw <= uvw}
  {D : Type@{w}} (Daf : IsAlgebraicallyFlabbyType@{uv w uvw} D)
  : IsAlgebraicInjectiveType@{u v w uv uw vw uvw} D.
Proof.
  intros X Y j isem f.
  snrefine (_; _).
  - intros y. srapply (Daf (hfiber j y) _ (fun x => f x.1)).1.
  - intros x. apply ((Daf (hfiber j (j x)) _ (fun x => f x.1)).2 (x; idpath (j x))).
Defined.

(** If D is algebraically ut,v-injective, then it is algebraically u,t-injective. *)
Definition resize_alg_inj@{u v w t ut uw vw tw uvt utw utvw | u <= ut, u <= uw, v <= vw, v <= uvt, w <= uw, w <= vw, w <= tw, t <= ut, t <= tw,
                                   ut <= uvt, ut <= utw, uw <= utw, vw <= utvw, tw <= utw, uvt <= utvw, utw <= utvw}
  {D : Type@{w}} (Dai : IsAlgebraicInjectiveType@{ut v w uvt utw vw utvw} D)
  : IsAlgebraicInjectiveType@{u t w ut uw tw utw} D.
Proof.
  apply alg_inj_alg_flab.
  apply (alg_flab_alg_inj Dai).
Defined.

(** ** Algebraic flabbiness with resizing axioms. *)

Section AssumePropResizing.
  Context `{PropResizing}.

  (** Algebraic flabbiness is independent of universes under propositional resizing. *)
  Definition universe_independent_alg_flab@{v u w vw uw | w <= vw, v <= vw, u <= uw, w <= uw}
    {D : Type@{w}} (Daf : IsAlgebraicallyFlabbyType@{v w vw} D)
    : IsAlgebraicallyFlabbyType@{u w uw} D.
  Proof.
    intros P PropP f.
    pose (e := (equiv_resize_hprop@{u v} P)^-1).
    destruct (Daf _ _ (f o e)) as [d af].
    exists d.
    intros p. lhs apply (af (e^-1 p)).
    apply ap. apply eisretr.
  Defined.

  (** Algebraic injectivity is independent of universes under propositional resizing. *)
  Definition universe_independent_alg_inj@{u v w u' v' uv uw vw u'v' u'w v'w uvw u'v'w | u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw, uv <= uvw, uw <= uvw, vw <= uvw,
                                             u' <= u'v', v' <= u'v', u' <= u'w, w <= u'w, v' <= v'w, w <= v'w, u'v' <= u'v'w, u'w <= u'v'w, v'w <= u'v'w}
    {D : Type@{w}} (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw uvw} D)
    : IsAlgebraicInjectiveType@{u' v' w u'v' u'w v'w u'v'w} D.
  Proof.
    apply alg_inj_alg_flab.
    apply universe_independent_alg_flab@{u u'v' w uw u'v'w}.
    apply (alg_flab_alg_inj Dai).
  Defined.

  (** Any algebraically injective type [D : Type@{u}] is a retract of [X -> Type@{u}] with [X : Type@{u}] -- Universe independent version of a previous statement. *)
  Definition retract_power_universe_alg_inj@{u su | u < su} `{Univalence}
    {D : Type@{u}} (Dai : IsAlgebraicInjectiveType@{u u u u u u u} D)
    : exists (X : Type@{u}) (s : D -> (X -> Type@{u})) (r : (X -> Type@{u}) -> D), r o s == idmap.
  Proof.
    refine (D; _).
    refine ((@paths D); _).
    apply universe_independent_alg_inj@{u u u u su u u u su u su u su} in Dai.
    apply (retract_power_universe_alg_usuinj D Dai).
  Defined.

  (** Any retract of a type family [X -> Type@{u}] is algebraically injective. *)
  Definition alg_inj_retract_power_universe@{u su | u < su}
    `{Univalence} (D : Type@{u}) {X : Type@{u}} {s : D -> (X -> Type@{u})}
    (r : (X -> Type@{u}) -> D) (retr : r o s == idmap)
    : IsAlgebraicInjectiveType@{u u u u u u u} D.
  Proof.
    apply (alg_inj_retract r retr).
    apply alg_inj_arrow.
    apply alg_inj_Type.
  Defined.

End AssumePropResizing.

(** ** Injectivity in terms of algebraic injectivity in the absence of resizing. *)

(** Algebraically injective types are injective. *)
Definition inj_alg_inj@{u v w uv uw vw uvw | u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw, uv <= uvw, uw <= uvw, vw <= uvw}
  (D : Type@{w}) (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw uvw} D)
  : IsInjectiveType@{u v w uv uw vw uvw} D.
Proof.
  intros X Y j isem f.
  apply tr.
  srapply Dai.
Defined.

(*Remove?*)
Definition ishprop_injectivity
  `{Funext} (D : Type@{w})
  : IsHProp@{t} (IsInjectiveType@{u v w uv uw vw uvw} D) := _.

(*Fix Universes*)
Definition inj_is_tr_alginj
  `{Funext} {D : Type@{w}} (mDai : merely (IsAlgebraicInjectiveType@{u v w uv uw vw uvw} D))
  : (IsInjectiveType@{u v w uv uw vw uvw} D).
Proof.
  strip_truncations.
  apply (inj_alg_inj D mDai).
Defined.

(** Injective types are retracts of any type that they embed into, in an unspecified way. *)
Definition retract_inj_embedding@{v w vw | v <= vw, w <= vw}
  (D : Type@{w}) {Y : Type@{v}} (j : D -> Y) (isem : IsEmbedding j)
  (Dai : IsAlgebraicInjectiveType@{w v w vw w vw vw} D)
  : merely { r | r o j == idmap }
  := tr (Dai _ _ _ _ idmap).

(** The retract of an injective type is injective. *)
Definition inj_retract
  `{Funext} {D' : Type@{w'}} {D : Type@{w}} (r : D -> D') {s : D' -> D}
  (retr : r o s == idmap) (Di : IsInjectiveType@{u v w uv uw vw uvw} D)
  : IsInjectiveType@{u v w' uv uw' vw' uvw'} D'.
Proof.
  intros X Y j isem f.
  pose proof (mD := Di X Y j isem (s o f)).
  strip_truncations; apply tr.
  snrefine (r o mD.1; _).
  intros x.
  rhs_V apply (retr (f x)).
  apply (ap r (mD.2 x)).
Defined.