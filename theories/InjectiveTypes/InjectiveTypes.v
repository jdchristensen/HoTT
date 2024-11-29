(* -*- mode: coq; mode: visual-line -*- *)
(** * Injective Types *)

(** ** Formalization of the paper: Injective Types in Univalent Mathematics by Martin Escardo. *)
(** Since the universe levels are important to many of the results here, we keep track of them explicitly as much as possible. Due to our inability to use the max and succesor operations within proofs, we instead construct these universes and thier associated posetal relations in the arguments of the functions. *)
(** In universe declarations, we use u, v, w, etc. as our typical universe variables. Our convention for the max of two universes u and v is uv, and the succesor of a universe u is su. Occasionally we write T for a top universe which is strictly larger than all other provided universes. We hope that later versions of Coq will allow us access to the max and successor operations and many of the cumbersome universe handing here can be greatly reduced. *)

Require Import Basics.
Require Import PropResizing.
Require Import Truncations.
Require Import Types.Universe Types.Unit Types.Prod Types.Empty Types.Forall Types.Sigma Types.Sum.
Require Import HFiber.
Require Import HProp.
Require Import PropResizing.
Require Import Constant.
Require Import ExcludedMiddle.

Require Import TypeFamKanExt.

Set Printing Universes.

Section UniverseStructure.
  Universes u v w uv uw vw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw.

  Definition IsInjectiveType@{uvw | uv <= uvw, uw <= uvw, vw <= uvw} (D : Type@{w})
    := forall (X : Type@{u}) (Y : Type@{v}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j)
      (f : X -> D), merely@{uvw} (sig@{vw uw} (fun f' => f' o j == f)).

  Definition IsAlgebraicInjectiveType@{} (D : Type@{w})
    := forall (X : Type@{u}) (Y : Type@{v}) (j : X -> Y) (isem : IsEmbedding@{u v uv} j)
      (f : X -> D), sig@{vw uw} (fun f' => f' o j == f).

  (** Contractible types are algebraically injective. *)
  Definition alg_inj_contr@{} (D : Type@{w}) (cD : Contr D)
    : IsAlgebraicInjectiveType@{} D.
  Proof.
    intros X Y j isem f.
    srefine (const (center D); _).
    intros x.
    apply (contr _).
  Defined.

  (** [Empty] is not algebraically injective. *)
  Definition not_alg_inj_empty@{}
    : IsAlgebraicInjectiveType@{} Empty -> Empty.
  Proof.
    intros Eai.
    snrefine ((Eai Empty Unit (Empty_rec@{v}) _ idmap).1 tt).
    rapply _; rapply mapinO_between_inO@{uv u v uv}.
  Defined.

End UniverseStructure.

(** [Type@{uv}] is algebraically u,v-injective in at least two ways. *)
Definition alg_inj_Type_sigma@{u v uv suv | u <= uv, v <= uv, uv < suv} `{Univalence}
  : IsAlgebraicInjectiveType@{u v suv uv suv suv} Type@{uv}.
Proof.
  intros X Y j isem f.
  snrefine (_; _).
  - exact (LeftKanTypeFamily f j).
  - intros x.
    apply (path_universe_uncurried (isext_leftkantypefamily _ _ isem _)).
Defined.

Definition alg_inj_Type_forall@{u v uv suv | u <= uv, v <= uv, uv < suv} `{Univalence}
  : IsAlgebraicInjectiveType@{u v suv uv suv suv} Type@{uv}.
Proof.
  intros X Y j isem f.
  snrefine (_; _).
  - exact (RightKanTypeFamily f j).
  - intros x. 
    apply (path_universe_uncurried (isext_rightkantypefamily _ _ isem _)).
Defined.

(** ** Constructions with algebraically injective types. *)

(** Retracts of algebraically injective types are algebraically injective. *)
Definition alg_inj_retract@{u v w w' uv uw vw uw' vw' | u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw, u <= uw', v <= vw', w' <= uw', w' <= vw'}
  {D' : Type@{w'}} {D : Type@{w}} (r : D -> D') {s : D' -> D}
  (retr : r o s == idmap) (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
  : IsAlgebraicInjectiveType@{u v w' uv uw' vw'} D'.
Proof.
  intros X Y j isem f.
  snrefine (_; _).
  - exact (r o (Dai _ _ _ _ (s o f)).1).
  - intros x. rhs_V apply (retr (f x)).
    apply (ap r ((Dai _ _ _ _ (s o f)).2 x)).
Defined.

Section UniverseStructure.
  Universes u v w t uv uw vw tw utw vtw.
  Constraint u <= uv, u <= uw, v <= vw, v <= uv, w <= uw, w <= vw, w <= tw, t <= tw,
    uw <= utw, vw <= vtw, tw <= utw, tw <= vtw.
  
  (** Dependent products are algebraically injective when all their factors are. *)
  Definition alg_inj_forall@{}
    `{Funext} {A : Type@{t}} (D : A -> Type@{w})
    (Dai : forall a, IsAlgebraicInjectiveType@{u v w uv uw vw} (D a))
    : IsAlgebraicInjectiveType@{u v tw uv utw vtw} (forall a, D a).
  Proof.
    intros X Y j isem f.
    snrefine (_; _). 
    - exact (fun y a => (Dai a _ _ _ _ (fun x => f x a)).1 y).
    - intros x. apply path_forall. intros a.
      exact ((Dai a _ _ _ _ (fun x => f x a)).2 x).
  Defined.

  Definition alg_inj_arrow@{}
    `{Funext} {A : Type@{t}} {D : Type@{w}}
    (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
    : IsAlgebraicInjectiveType@{u v tw uv utw vtw} (A -> D).
  Proof.
    apply (alg_inj_forall _).
    intros a.
    apply Dai.
  Defined.

End UniverseStructure.

(** Algebraically injective types are retracts of any type that they embed into. *)
Definition retract_alg_inj_embedding@{v w vw | v <= vw, w <= vw}
  (D : Type@{w}) {Y : Type@{v}} (j : D -> Y) (isem : IsEmbedding j)
  (Dai : IsAlgebraicInjectiveType@{w v w vw w vw} D)
  : { r | r o j == idmap }
  := Dai _ _ _ _ idmap.

(** Any algebraically u,u^+-injective type [X : Type@{u}], is a retract of [X -> Type@{u}]. *)
Definition retract_power_universe_alg_usuinj@{u su | u < su} `{Univalence}
  (D : Type@{u}) (Dai : IsAlgebraicInjectiveType@{u su u su u su} D)
  : { r : (D -> Type@{u}) -> D | r o (@paths D) == idmap }
  := retract_alg_inj_embedding D (@paths D) isembedding_paths Dai.

(** ** Algebraic flabbiness and resizing constructions. *)

(** If [D : Type@{u}] is algebraically u,u^+-injective, then it is algebraically u,u-injective. *)
(** Note that this proof is made trivial by the library's handeling of universes. *)
Definition alg_uuinj_alg_usu_inj@{u su | u < su}
  (D : Type@{u}) (Dai : IsAlgebraicInjectiveType@{u su u su u su} D)
  : IsAlgebraicInjectiveType@{u u u u u u} D
  := Dai.

Definition IsAlgebraicFlabbyType@{u w uw | u <= uw, w <= uw} (D : Type@{w})
  := forall (P : Type@{u}) (PropP : IsHProp P) (f : P -> D),
    { d : D | forall p : P, d = f p}.
(** We can think of algebraic flabbiness as algebraic injectivity, but only ranging over embeddings of propositions into the unit type. *)

(** Algebraic flabbiness of a type [D] is equivalent to the statment that all conditionally constant functions [X -> D] are constant. *)
Definition cconst_is_const_cond@{u w uw suw | u <= uw, w <= uw, uw < suw}
  (D : Type@{w}) : Type@{suw}
  := forall (X : Type@{u}) (f : X -> D),
    ConditionallyConstant@{u w uw} f -> sig@{uw uw} (fun d => forall x, d = f x).

Definition alg_flab_cconst_is_const@{u w uw suw | u <= uw, w <= uw, uw < suw}
  (D : Type@{w}) (ccond : cconst_is_const_cond@{u w uw suw} D)
  : IsAlgebraicFlabbyType@{u w uw} D.
Proof.
  intros P PropP f.
  apply (ccond P f).
  apply (cconst_factors_hprop _ _ idmap f).
  reflexivity.
Defined.

Definition cconst_is_const_alg_flab@{u w uw suw | u <= uw, w <= uw, uw < suw}
  (D : Type@{w}) (Daf : IsAlgebraicFlabbyType@{u w uw} D)
  : cconst_is_const_cond@{u w uw suw} D.
Proof.
  intros X f [f' e].
  srefine ((Daf _ _ f').1; _).
  intros x.
  apply ((Daf _ _ f').2 (tr x) @ (e x)).
Defined.

(** We include two direct proofs of the algebraic flabbiness of [Type], instead of combining [alg_inj_alg_flab] with the previous proofs of algebraic injectivity, for better computations later. *)
Definition alg_flab_Type_sigma@{u su | u < su} `{Univalence}
  : IsAlgebraicFlabbyType@{u su su} Type@{u}.
Proof.
  intros P PropP A.
  srefine (sig@{u u} (fun p => A p); _).
  intros p.
  transparent assert (C : (Contr P)).
    - srapply contr_inhabited_hprop. exact p.
    - apply path_universe_uncurried.
      apply (@equiv_contr_sigma _ _ C).
Defined.

Definition alg_flab_Type_forall@{u su | u < su} `{Univalence}
  : IsAlgebraicFlabbyType@{u su su} Type@{u}.
Proof.
  intros P PropP A.
  srefine (forall p : P, A p; _).
  intros p.
  transparent assert (C : (Contr P)).
    - srapply contr_inhabited_hprop. exact p.
    - apply path_universe_uncurried.
      snrapply (@equiv_contr_forall _ _ C).
Defined.

Section UniverseStructure.
  Universes u v w uv uw vw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw.

  (** Algebraically u,v-injective types are algebraically u-flabby. *)
  Definition alg_flab_alg_inj@{}
    {D : Type@{w}} (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
    : IsAlgebraicFlabbyType@{u w uw} D.
  Proof.
    intros P PropP f.
    snrefine (_; _).
    - srapply ((Dai _ _ (const_tt P) _ f).1 tt).
    - intros p. apply (Dai _ _ (const_tt P) _ f).2.
  Defined.

  (** Algebraically uv-flabby types are algebraically u,v-injective. *)
  Definition alg_inj_alg_flab@{uvw | uv <= uvw, uw <= uvw, vw <= uvw}
    {D : Type@{w}} (Daf : IsAlgebraicFlabbyType@{uv w uvw} D)
    : IsAlgebraicInjectiveType@{u v w uv uw vw} D.
  Proof.
    intros X Y j isem f.
    snrefine (_; _).
    - intros y. srapply (Daf (hfiber j y) _ (fun x => f x.1)).1.
    - intros x. apply ((Daf (hfiber j (j x)) _ (fun x => f x.1)).2 (x; idpath (j x))).
  Defined.

End UniverseStructure.

(** If D is algebraically ut,v-injective, then it is algebraically u,t-injective. *)
Definition resize_alg_inj@{u v w t ut uw vw tw uvt utw | u <= ut, u <= uw, v <= vw, v <= uvt, w <= uw, w <= vw, w <= tw, t <= ut, t <= tw,
                            ut <= uvt, ut <= utw, uw <= utw, tw <= utw}
  {D : Type@{w}} (Dai : IsAlgebraicInjectiveType@{ut v w uvt utw vw} D)
  : IsAlgebraicInjectiveType@{u t w ut uw tw} D.
Proof.
  apply alg_inj_alg_flab.
  apply (alg_flab_alg_inj Dai).
Defined.

(** ** Injectivity of subuniverses. *)

(** A subuniverse which contains all propositions, and is closed under Sigma or Pi types, as formulated below, is algebraically flabby, and hence algebraically injective. *)
Definition alg_flab_subuniverse_sigma@{u su | u < su} `{Univalence}
  (O : Subuniverse@{u}) (cHProp : forall (P : Type@{u}) (PropP : IsHProp P), In O P)
  (cSig : forall (X : Type@{u}) (Y : X -> Type@{u}) (YxinO : forall x : X, In O (Y x)),
    In O (sig@{u u} (fun x : X => Y x)))
  : IsAlgebraicFlabbyType@{u su su} (Type_@{u su} O).
Proof.
  intros Q PropQ f.
  transparent assert (d : (Type_ O)).
  { apply (sig@{u u} (pr1 o f); cSig _ _ _). }
  srefine (d; _).
  intros q.
  srapply path_sigma.
  - apply path_universe_uncurried.
    transparent assert (C : (Contr Q)).
    * srapply contr_inhabited_hprop; exact q.
    * snrapply (@equiv_contr_sigma _ _ C).
  - apply path_ishprop.
Defined.

Definition alg_flab_subuniverse_forall@{u su | u < su} `{Univalence}
  (O : Subuniverse@{u}) (cHProp : forall (P : Type@{u}) (PropP : IsHProp P), In O P)
  (cForall : forall (X : Type@{u}) (Y : X -> Type@{u}) (YxinO : forall x, In O (Y x)),
    In O (forall x, Y x))
  : IsAlgebraicFlabbyType@{u su su} (Type_@{u su} O).
Proof.
  intros Q PropQ f.
  transparent assert (d : (Type_ O)).
  { apply (forall q : Q, (f q).1; cForall _ _ _). }
  srefine (d; _).
  intros q.
  srapply path_sigma.
  - apply path_universe_uncurried.
    transparent assert (C : (Contr Q)).
    * srapply contr_inhabited_hprop; exact q.
    * snrapply (@equiv_contr_forall _ _ C).
  - apply path_ishprop.
Defined.

(* MOVE TO Truncations.Core BEFORE "A few special things about the (-1)-truncation" *)
(** The type of contractible types is contractible. *)
Definition contr_tr_minus_2@{u su | u < su} `{Univalence}
  : Contr (Type_@{u su} (Tr (-2))).
Proof.
  apply (Build_Contr _ (exist@{su su} _ (Unit : Type@{u}) (inO_tr_istrunc _))).
  intros [C ContrC].
  apply equiv_path_sigma_hprop.
  apply path_universe_uncurried.
  symmetry; apply equiv_contr_unit.
Defined.

(** The type of n-truncated types is algebraically injective for all n. *)
Definition alg_inj_ntrunc@{u su | u < su} `{Univalence} (n : trunc_index)
  : IsAlgebraicFlabbyType@{u su su} (Type_@{u su} (Tr n)).
Proof.
  destruct n.
  - apply alg_flab_alg_inj@{u u su u su su}.
    apply alg_inj_contr.
    apply contr_tr_minus_2@{u su}.
  - apply alg_flab_subuniverse_forall.
    * intros P PropP. apply (@istrunc_leq (-1) n.+1 tt _ _).
    * apply _.
Defined.

(** ** Algebraic flabbiness with resizing axioms. *)

Section AssumePropResizing.
  Context `{PropResizing}.

  (** Algebraic flabbiness is independent of universes under propositional resizing. *)
  Definition universe_independent_alg_flab@{v u w vw uw | w <= vw, v <= vw, u <= uw, w <= uw}
    {D : Type@{w}} (Daf : IsAlgebraicFlabbyType@{v w vw} D)
    : IsAlgebraicFlabbyType@{u w uw} D.
  Proof.
    intros P PropP f.
    pose (e := (equiv_smalltype@{v u} P)).
    destruct (Daf _ (istrunc_equiv_istrunc _ e^-1) (f o e)) as [d af].
    exists d.
    intros p. lhs apply (af (e^-1 p)).
    apply ap. apply eisretr.
  Defined.

  (** Algebraic injectivity is independent of universes under propositional resizing. *)
  Definition universe_independent_alg_inj@{u v w u' v' uv uw vw u'v' u'w v'w u'v'w | u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
                                            u' <= u'v', v' <= u'v', u' <= u'w, w <= u'w, v' <= v'w, w <= v'w, u'v' <= u'v'w, u'w <= u'v'w, v'w <= u'v'w}
    {D : Type@{w}} (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
    : IsAlgebraicInjectiveType@{u' v' w u'v' u'w v'w} D.
  Proof.
    apply alg_inj_alg_flab.
    apply universe_independent_alg_flab@{u u'v' w uw u'v'w}.
    apply (alg_flab_alg_inj Dai).
  Defined.

  (** Any algebraically injective type [D : Type@{u}] is a retract of [X -> Type@{u}] with [X : Type@{u}] -- Universe independent version of [retract_power_universe_alg_usuinj]. *)
  Definition retract_power_universe_alg_inj@{u su | u < su} `{Univalence}
    {D : Type@{u}} (Dai : IsAlgebraicInjectiveType@{u u u u u u} D)
    : exists (X : Type@{u}) (s : D -> (X -> Type@{u})) (r : (X -> Type@{u}) -> D), r o s == idmap.
  Proof.
    refine (D; _).
    refine ((@paths D); _).
    apply (retract_power_universe_alg_usuinj D).
    apply (universe_independent_alg_inj@{u u u u su u u u su u su su} Dai).
  Defined.

End AssumePropResizing.

(** Any retract of a type family [X -> Type@{u}] is algebraically injective. This is the opposite result as above, classifying algebraically injective types, independent of universes. It should be noted that this direction of the if and only if does not depend on propositional resizing. *)
Definition alg_inj_retract_power_universe@{u su | u < su}
  `{Univalence} (D : Type@{u}) {X : Type@{u}} {s : D -> (X -> Type@{u})}
  (r : (X -> Type@{u}) -> D) (retr : r o s == idmap)
  : IsAlgebraicInjectiveType@{u u u u u u} D.
Proof.
  apply (alg_inj_retract r retr).
  apply alg_inj_arrow.
  apply alg_inj_Type_sigma.
Defined.

(** ** Injectivity in terms of algebraic injectivity in the absence of resizing. *)

Section UniverseStructure.
  Universes u v w uv uw vw uvw.
  Constraint u <= uv, v <= uv, u <= uw, w <= uw, v <= vw, w <= vw,
    uv <= uvw, uw <= uvw, vw <= uvw.

  (** Algebraically injective types are injective. *)
  Definition inj_alg_inj@{}
    (D : Type@{w}) (Dai : IsAlgebraicInjectiveType@{u v w uv uw vw} D)
    : IsInjectiveType@{u v w uv uw vw uvw} D.
  Proof.
    intros X Y j isem f.
    apply tr.
    srapply Dai.
  Defined.

  (** The propositional truncation of algebraic injectivity implies injectivity. *)
  Definition inj_merely_alg_inj@{T | uvw < T}
    `{Funext} {D : Type@{w}}
    (mDai : merely@{T} (IsAlgebraicInjectiveType@{u v w uv uw vw} D))
    : ((IsInjectiveType@{u v w uv uw vw uvw} D) : Type@{T}).
  Proof.
    revert mDai.
    nrapply Trunc_rec@{T T}. (* Manually stripping truncations so as to control universe variables. *)
    - repeat (nrapply istrunc_forall@{T T T}; intro).
      apply istrunc_truncation.
    - intro Dai.
      apply (inj_alg_inj@{} D Dai).
  Defined.

  (** The retract of an injective type is injective. *)
  Definition inj_retract@{w' uw' vw' uvw' T | u <= uw', v <= vw', w' <= uw', w' <= vw', uv <= uvw', uw' <= uvw', vw' <= uvw', uvw < T, uvw' < T}
    `{Funext} {D' : Type@{w'}} {D : Type@{w}} (r : D -> D') {s : D' -> D}
    (retr : r o s == idmap) (Di : IsInjectiveType@{u v w uv uw vw uvw} D)
    : IsInjectiveType@{u v w' uv uw' vw' uvw'} D'.
  Proof.
    intros X Y j isem f.
    pose proof (mD := Di X Y j isem (s o f)).
    revert mD.
    nrapply Trunc_rec@{T T}.
    - apply istrunc_truncation.
    - intros [g e].
      apply tr.
      snrefine (r o g; _).
      intros x.
      rhs_V apply (retr (f x)).
      apply (ap r (e x)).
  Defined.

End UniverseStructure.

(** Injective types are retracts of any type that they embed into, in an unspecified way. *)
Definition merely_retract_inj_embedding@{v w vw svw | v <= vw, w <= vw, vw < svw}
  (D : Type@{w}) {Y : Type@{v}} (j : D -> Y) (isem : IsEmbedding j)
  (Di : IsInjectiveType@{w v w vw w vw vw} D)
  : merely@{svw} { r | r o j == idmap }
  := (Di _ _ _ _ idmap).

(** The power of an injective type is injective. *)
Definition inj_arrow@{u v w t uv ut vt tw uvt utw vtw utvw | u <= uv, v <= uv, u <= ut, t <= ut, v <= vt, t <= vt, t <= tw, w <= tw,
                        uv <= uvt, ut <= uvt, vt <= uvt, ut <= utw, tw <= utw, vt <= vtw, tw <= vtw, uvt <= utvw, utw <= utvw, vtw <= utvw}
  `{Funext} {A : Type@{t}} (D : Type@{w})
  (Di : IsInjectiveType@{ut vt w uvt utw vtw utvw} D)
  : IsInjectiveType@{u v tw uv utw vtw utvw} (A -> D).
Proof.
  intros X Y j isem f.
  assert (embId : IsEmbedding (fun a : A => a)).
  - nrapply istruncmap_mapinO_tr. rapply _.
  - pose proof (mD := Di (X * A) (Y * A) (functor_prod j idmap)
      (istruncmap_functor_prod@{u v t t ut vt uvt uvt uv t} _ _ _) (uncurry f)).
    revert mD.
    nrapply Trunc_rec@{utvw utvw}.
    * apply istrunc_truncation.
    * intros [g e].
      apply tr.
      refine (fun y a => g (y, a); _).
      intros x. apply path_forall. intros a.
      apply (e (x, a)).
Defined.

(** Any u,u^+-injective type [X : Type@{u}], is a retract of [X -> Type@{u}] in an unspecified way. *)
Definition merely_retract_power_universe_inj@{u su ssu | u < su, su < ssu}
  `{Univalence} (D : Type@{u}) (Di : IsInjectiveType@{u su u su u su su} D)
  : merely@{su} (sig@{su su} (fun r => r o (@paths D) == idmap))
  := merely_retract_inj_embedding D (@paths D) isembedding_paths Di.

(** Inverse of [inj_merely_alg_inj] modulo universes. *)
Definition merely_alg_inj_inj@{u su ssu | u < su, su < ssu} `{Univalence}
  (D : Type@{u}) (Di : IsInjectiveType@{u su u su u su su} D)
  : merely@{su} (IsAlgebraicInjectiveType@{u u u u u u} D).
Proof.
  srefine (Trunc_functor (-1) _ (merely_retract_power_universe_inj D Di)).
  intros [r retr].
  apply (alg_inj_retract_power_universe D r retr).
Defined.

(** ** The equivalence of excluded middle with the (algebraic) injectivity of pointed types. *)

(** Assuming excluded middle, all pointed types are algebraically flabby (and thus algebraically injective). *)
Definition alg_flab_pted_lem@{u w uw | u <= uw, w <= uw}
  `{ExcludedMiddle} {D : Type@{w}} (d : D)
  : IsAlgebraicFlabbyType@{u w uw} D.
Proof.
  intros P PropP f.
  case (LEM P _).
  - intros p. srefine (f p; _).
    intros q. apply (ap _ (path_ishprop _ _)).
  - intros np. srefine (d; _).
    intros p. apply (Empty_rec (np p)).
Defined.

(*MOVE ELSEWHERE*)
(** The decidablility of a proposition is a proposition. *)
Definition hprop_decidibility_prop `{Funext} P (PropP : IsHProp P)
  : IsHProp (Decidable P).
Proof.
  rapply ishprop_sum.
  intros p np.
  apply (Empty_rec (np p)).
Defined.

(** If the type [P + ~P + Unit] is algebraically flabby for P a proposition, then P is decidable. *)
Definition decidable_alg_flab_hprop@{w} `{Funext} (P : Type@{w}) (PropP : IsHProp P)
  (Paf : IsAlgebraicFlabbyType@{w w w} ((P + ~P) + (Unit : Type@{w})))
  : Decidable P.
Proof.
  transparent assert (f : (P + ~P -> ((P + ~P) + Unit))).
  { intros p; destruct p.
    - apply (inl (inl p)).
    - apply (inl (inr n)). }
  assert (l : {d | forall z, d = f z}).
  { apply Paf. rapply hprop_decidibility_prop@{w w w w}. }
  assert (delta : (forall d', l.1 = d' -> (Decidable P))).
  { intros d' r; destruct d'.
    - apply s.
    - assert (np := fun p => (inl_ne_inr _ _ ((l.2 (inl p))^ @ r))).
      assert (nnp := fun np' => (inl_ne_inr _ _ ((l.2 (inr np'))^ @ r))).
      apply (Empty_rec (nnp np)). }
  apply (delta l.1 idpath).
Defined.

(** If all pointed types are algebraically flabby, then excluded middle holds. *)
Definition lem_pted_types_alg_flab@{w} `{Funext}
  (ptaf: forall (D : Type@{w}), D -> IsAlgebraicFlabbyType@{w w w} D)
  : ExcludedMiddle_type@{w}.
Proof.
  intros P PropP.
  rapply decidable_alg_flab_hprop.
  apply ptaf.
  apply (inr tt).
Defined.