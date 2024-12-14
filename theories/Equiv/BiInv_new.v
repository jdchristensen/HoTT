Require Import Basics Types.Prod Types.Equiv Types.Sigma Types.Universe.

Local Open Scope path_scope.
Generalizable Variables A B f.

(** * Bi-invertible maps *)

(** A map is "bi-invertible" if it has both a section and a retraction, not necessarily the same.  This definition of equivalence was proposed by Andre Joyal. *)

Class IsBiInv {A B : Type} (e : A -> B) := {
  sect_biinv : B -> A ;
  retr_biinv : B -> A ;
  eisretr_biinv : e o sect_biinv == idmap ;
  eissect_biinv : retr_biinv o e == idmap ;
}.

Arguments sect_biinv {A B}%_type_scope e%_function_scope {_} _.
Arguments retr_biinv {A B}%_type_scope e%_function_scope {_} _.
Arguments eisretr_biinv {A B}%_type_scope e%_function_scope {_} _.
Arguments eissect_biinv {A B}%_type_scope e%_function_scope {_} _.

(** If [e] is bi-invertible, then the retraction and the section of [e] are equal. *)
Definition sect_retr_homotopic_biinv {A B : Type} (f : A -> B) `{bi : !IsBiInv f}
  : sect_biinv f == retr_biinv f.
Proof.
  revert bi.
  intros [h g r s].
  exact (fun y => (s (h y))^ @ ap g (r y)).
Defined.

(** The record is equivalent to a product type. This is used below in a 'product of contractible types is contractible' argument. *)
Definition prod_isbiinv (A B : Type) `{f: A -> B}
  : {g : B -> A & g o f == idmap} * {h : B -> A & f o h == idmap} <~> IsBiInv f.
Proof.
    make_equiv.
Defined.

Record EquivBiInv A B := {
  equiv_fun_biinv :> A -> B ;
  equiv_isequiv_biinv :> IsBiInv equiv_fun_biinv
}.

Existing Instance equiv_isequiv_biinv.

Definition issig_equivbiinv (A B : Type)
  : {f : A -> B & IsBiInv f} <~> EquivBiInv A B.
Proof.
  issig.
Defined.

(** From a bi-invertible map, we can construct a half-adjoint equivalence in two ways. Here we take the inverse to be the retraction. *)
Global Instance isequiv_isbiinv {A B : Type} (f : A -> B) `{bi : !IsBiInv f} : IsEquiv f.
Proof.
  revert bi.
  intros [h g r s].
  exact (isequiv_adjointify f g
    (fun x => ap f (ap g (r x)^ @ s (h x)) @ r x)
    s).
Defined.

(** Here we take the inverse to be the section. *)
Definition isequiv_isbiinv' {A B : Type} (f : A -> B) `{bi : !IsBiInv f} : IsEquiv f.
Proof.
  snrapply isequiv_adjointify.
  - apply (sect_biinv f).
  - apply eisretr_biinv.  (* We provide proof of eissect, but it gets modified. *)
  - intro a.
    lhs nrapply sect_retr_homotopic_biinv.
    apply eissect_biinv.
Defined.

Definition isbiinv_isequiv `(f : A -> B)
  : IsEquiv f -> IsBiInv f.
Proof.
  intros [g s r adj].
  exact (Build_IsBiInv _ _ f g g s r).
Defined.

Definition iff_isbiinv_isequiv `(f : A -> B)
  : IsBiInv f <-> IsEquiv f.
Proof.
  split.
  - apply isequiv_isbiinv.
  - apply isbiinv_isequiv.
Defined.

(** This here uses implicitly that the product of contractible types is contractible. *)
Global Instance ishprop_isbiinv `{Funext} `(f : A -> B) : IsHProp (IsBiInv f) | 0.
Proof.
  apply hprop_inhabited_contr.
  intros bif.
  srapply (contr_equiv' _ (prod_isbiinv A B)).
Defined.

Definition equiv_isbiinv_isequiv `{Funext} `(f : A -> B)
  : IsBiInv f <~> IsEquiv f.
Proof.
  apply equiv_iff_hprop_uncurried, iff_isbiinv_isequiv.
Defined.

(* Some lemmas to send equivalences and biinvertible maps back and forth. *)

Definition equiv_biinv A B (f : EquivBiInv A B) : A <~> B := Build_Equiv A B f _.

Definition biinv_equiv A B  (e : A <~> B):  EquivBiInv A B := Build_EquivBiInv A B e (isbiinv_isequiv e (equiv_isequiv e)).

Definition equiv_biinv_equiv `{Funext} A B
  : EquivBiInv A B <~> (A <~> B) .
Proof.
  refine ((issig_equiv A B) oE _ oE (issig_equivbiinv A B)^-1).
  rapply (equiv_functor_sigma_id equiv_isbiinv_isequiv).
Defined.

Definition equiv_idmap_biinv (A : Type) : EquivBiInv A A.
Proof.
  by nrefine (Build_EquivBiInv A A idmap (Build_IsBiInv A A idmap idmap idmap _ _ )).
Defined.

(* TODO: move this to right after equiv_inj in PathGroupoids.v *)
Definition equiv_inj_comp `(f : A -> B) `{IsEquiv A B f} {x y : A}
  (p : f x = f y)
  : ap f (equiv_inj f p) = p.
Proof.
  unfold equiv_inj.
  apply eisretr.
Defined.

(** We define what it means for two maps [f] and [g] to be compatible with two equivalences [e] and [e'] in a commutative square. *)
Section EquivalenceCompatibility.

  Context (A B C D : Type).
  Context (e : EquivBiInv A B) (e' : EquivBiInv C D) (f : A -> C) (g : B -> D).

  Let s := sect_biinv e.
  Let r := retr_biinv e.
  Let re := eissect_biinv e : r o e == idmap.
  Let es := eisretr_biinv e: e o s == idmap.
  Let s' := sect_biinv e'.
  Let r' := retr_biinv e'.
  Let re' := eissect_biinv e' : r' o e' == idmap.
  Let es' := eisretr_biinv e' : e' o s' == idmap.

  Definition helper_r (pe : e' o f == g o e) : r' o g o e == f o r o e.
  Proof.
    intro x.
    exact ((ap r' (pe x))^ @ (re' (f x) @ (ap f (re x))^)).
  Defined.

  Definition helper_s (pe : e' o f == g o e) : e' o s' o g == e' o f o s.
  Proof.
    intro y.
    exact (es' (g y) @ (ap g (es y))^ @ (pe (s y))^).
  Defined.

  (** A record that contains all the data witnessing what it means for two maps [f] and [g] between biinvertible maps [e] and [e'] to be compatible with the biinvertible structure. *)
  Record prBiInv
  := {
    pe : forall (x : A), e' (f x) = g (e x);
    pr : forall (y : B), r' (g y) = f (r y);
    ps : forall (y : B), s' (g y) = f (s y);
    pre : forall (x : A), re' (f x) = ap r' (pe x) @ pr (e x) @ ap f (re x);
    pes : forall (y : B), es' (g y) = ap e' (ps y) @ pe (s y) @ ap g (es y);
  }.

  (** To be compatible it suffices to commute with [e] and [e']. *)
  Definition compat_implies_prBiInv (pe : forall (x : A), e' (f x) = g (e x))
    : prBiInv.
  Proof.
    srapply Build_prBiInv.
    - exact pe.
    - apply (equiv_ind e).
      apply (helper_r pe).
    - intro y.
      apply (equiv_inj e'); cbn.
      apply (helper_s pe).
    - intro x.
      rewrite equiv_ind_comp.
      apply moveL_pM.
      apply moveL_Mp.
      reflexivity.
    - intro y; cbn beta.
      rewrite equiv_inj_comp.
      apply moveL_pM.
      apply moveL_pM.
      reflexivity.
  Defined.

End EquivalenceCompatibility.
