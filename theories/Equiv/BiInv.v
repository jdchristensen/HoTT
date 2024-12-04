Require Import Basics Types.Prod Types.Equiv Types.Sigma Types.Universe.

Local Open Scope path_scope.
Generalizable Variables A B f.

(** * Bi-invertible maps *)

(** A map is "bi-invertible" if it has both a section and a retraction, not necessarily the same.  This definition of equivalence was proposed by Andre Joyal. *)

Definition BiInv {A B : Type} (f : A -> B) : Type
  := {g : B -> A & g o f == idmap} * {h : B -> A & f o h == idmap}.

Existing Class BiInv.

(** It seems that the easiest way to show that bi-invertibility is equivalent to being an equivalence is also to show that both are h-props and that they are logically equivalent. *)

(** From a bi-invertible map, we can construct a half-adjoint equivalence in two ways. Here we take the inverse to be the retraction. *)
Global Instance isequiv_biinv {A B : Type} (f : A -> B) `{bi : !BiInv f} : IsEquiv f.
Proof.
  destruct bi as [[g s] [h r]].
  exact (isequiv_adjointify f g
    (fun x => ap f (ap g (r x)^ @ s (h x)) @ r x)
    s).
Defined.


Definition biinv_isequiv `(f : A -> B)
  : IsEquiv f -> BiInv f.
Proof.
  intros [g s r adj].
  exact ((g; r), (g; s)).
Defined.

Definition iff_biinv_isequiv `(f : A -> B)
  : BiInv f <-> IsEquiv f.
Proof.
  split.
  - apply isequiv_biinv.
  - apply biinv_isequiv.
Defined.

Global Instance ishprop_biinv `{Funext} `(f : A -> B) : IsHProp (BiInv f) | 0.
Proof.
  apply hprop_inhabited_contr.
  intros bif.
  apply @contr_prod.
  (* For this, we've done all the work already. *)
  - rapply contr_retr_equiv.
  - rapply contr_sect_equiv.
Defined.

Definition equiv_biinv_isequiv `{Funext} `(f : A -> B)
  : BiInv f <~> IsEquiv f.
Proof.
  apply equiv_iff_hprop_uncurried, iff_biinv_isequiv.
Defined.


(** These are some projections *)
(* jTODO Eventually  make a Record with fields with appropriate names,
trying to parallel Equiv and IsEquiv as much as possible.  E.g. instead of "issec_binv"
use "eissect_biinv" with the "e" and the start and the "t" at the end.  And I think
it should be "_biinv", not "_binv". *)
(* TODO: The "BiInv f" parts should be moved to the left of the colon and be made implicit. "f" should be explicit. *)
Definition ret_binv `{f : A -> B}
  : BiInv f -> (B -> A).
Proof.
  intro X.
  exact (pr1 (fst X)).
Defined.

Definition sec_binv `{f : A -> B}
  : BiInv f -> (B -> A).
Proof.
  intro X.
  exact (pr1 (snd X)).
Defined.

Definition isret_binv `{f : A -> B}
  : forall (e: BiInv f), f o (sec_binv e) == idmap.
Proof.
  intro.
  simpl.
  exact (pr2 (snd e)).
Defined.

Definition issec_binv `{f : A -> B}
  : forall (e: BiInv f), (ret_binv e) o f == idmap.
Proof.
  intro.
  simpl.
  exact (pr2 (fst e)).
Defined.


(** A record summing over all bi-invertible maps*)

Record EquivBiInv A B := {
  equiv_fun_binv :> A -> B ;
  equiv_isequiv_binv :> BiInv equiv_fun_binv
}.

Existing Instance equiv_isequiv_binv.

Definition issig_equivbiinv (A B : Type)
  : {f : A -> B & BiInv f} <~> EquivBiInv A B.
Proof.
  issig.
Defined.

(* Some lemmas to send equivalences and biinvertible maps back and forth.*)

(* TODO: This should be called equiv_ not isequiv_ *)
Definition isequiv_biinv_record A B (f : EquivBiInv A B)
  : A <~> B
  := Build_Equiv A B f _.

(* TODO: change isequiv to equiv in name: *)
Definition biinv_isequiv_record A B
  :  A <~> B -> EquivBiInv A B.
Proof.
  intros [f e].
  exact (Build_EquivBiInv A B f (biinv_isequiv f e)).
Defined.

(* TODO: Delete this.  "iff" is useful between hprops, but not in cases like this. *)
Definition iff_biinv_isequiv_record A B
  : EquivBiInv A B <-> A <~> B.
Proof.
  split.
  - apply isequiv_biinv_record.
  - apply biinv_isequiv_record.
Defined.

Definition equiv_biinv_isequiv_record `{Funext} A B
  : EquivBiInv A B <~> (A <~> B) .
Proof.
  refine ((issig_equiv A B) oE _ oE (issig_equivbiinv A B)^-1).
  rapply (equiv_functor_sigma_id equiv_biinv_isequiv).
Defined.

Definition equiv_idmap_binv (A : Type) 
  : (EquivBiInv A A).
Proof.
  by nrefine (Build_EquivBiInv A A idmap ((idmap; _), (idmap; _))).
Defined.


(** TODO chnage BiInv to IsBinv and make it also a record*)
(** A typeclass that includes the data making [f] into a bi-invertible equivalence.
Class IsBinv {A B : Type} (f : A -> B) := {
  sec_proj : B -> A ;
  ret_proj : B -> A ;
  eisretr : f o sec_proj == idmap ;
  eissect : ret_proj o f == idmap ;
}.

Record EquivBiInv A B := {
  equiv_fun_binv : A -> B ;
  equiv_isequiv_binv : IsBinv equiv_fun_binv
}. *)


Section BiInvProperties.

  (* TODO: The following things should go right after the definition of BiInv, but they are here so I can make use of the accessor functions.  They are no longer needed in the proof below, but should probably still be part of the general theory of bi-invertible maps.  In particular, it seems like it might be useful to have isequiv_biinv'. *)

  (** If [e] is bi-invertible, then the retraction and the section of [e] are equal. *)
  Definition sec_ret_homotopic_binv {A B : Type} (f : A -> B) `{bi : !BiInv f}
    : sec_binv bi == ret_binv bi.
  Proof.
    destruct bi as [[g s] [h r]].
    exact (fun y => (s (h y))^ @ ap g (r y)).
  Defined.

(** TODO move up after definition*)
(** Here we take the inverse to be the section. *)
Definition isequiv_biinv' {A B : Type} (f : A -> B) `{bi : !BiInv f} : IsEquiv f.
Proof.
  snrapply isequiv_adjointify.
  - apply (sec_binv bi).
  - apply isret_binv.  (* We provide proof of eissect, but it gets modified. *)
  - intro a.
    lhs nrapply sec_ret_homotopic_binv.
    apply issec_binv.
Defined.

End BiInvProperties.

(* TODO: move this to right after equiv_inj in PathGroupoids.v *)
Definition equiv_inj_comp `(f : A -> B) `{IsEquiv A B f} {x y : A}
  (p : f x = f y)
  : ap f (equiv_inj f p) = p.
Proof.
  unfold equiv_inj.
  apply eisretr.
Defined.

Section DansAttempt.

  Context (A B C D : Type).
  Context (e : EquivBiInv A B) (e' : EquivBiInv C D) (f : A -> C) (g : B -> D).

  Let s := sec_binv e.
  Let r := ret_binv e.
  Let re := issec_binv e : r o e == idmap.
  Let es := isret_binv e : e o s == idmap.
  Let s' := sec_binv e'.
  Let r' := ret_binv e'.
  Let re' := issec_binv e' : r' o e' == idmap.
  Let es' := isret_binv e' : e' o s' == idmap.

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

  Record prBiInv
  := {
    pe : forall (x : A), e' (f x) = g (e x);
    pr : forall (y : B), r' (g y) = f (r y);
    ps : forall (y : B), s' (g y) = f (s y);
    pre : forall (x : A), re' (f x) = ap r' (pe x) @ pr (e x) @ ap f (re x);
    pes : forall (y : B), es' (g y) = ap e' (ps y) @ pe (s y) @ ap g (es y);
  }.

  Definition compat_implies_prBiInv' (pe : forall (x : A), e' (f x) = g (e x))
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

End DansAttempt.


Section BiInvCompatUnivalence.
Context `{Univalence}.

(* Definition equiv_path_binv (A B : Type@{u}) (p : A = B) : EquivBiInv A B 
  := (((equiv_fun (equiv_biinv_isequiv_record A B)^-1) o (equiv_path A B)) p). *)

Definition equiv_path_binv (A B : Type@{u}) : (A = B) <~> EquivBiInv A B
  := (equiv_biinv_isequiv_record A B)^-1 oE equiv_equiv_path A B. 


(** Paulin-Mohring style *)
Theorem equiv_induction_binv {U : Type} (P : forall V, EquivBiInv U V -> Type)
  : (P U (equiv_idmap_binv U)) -> (forall V (w :  EquivBiInv U V), P V w).
Proof.
  intros H0 V w.
  srapply (equiv_ind (equiv_path_binv U V)).
  - intro p.
    induction p.
    exact H0.
Defined.

(** Martin-Lof style *)
Theorem equiv_induction_binv' 
  (P : forall U V, (EquivBiInv U V) -> Type)
  : (forall T, P T T (equiv_idmap_binv T)) -> (forall U V (w : (EquivBiInv U V)), P U V w).
Proof.
  intros H0 U V w.
  srapply (equiv_ind (equiv_path_binv U V)).
  - intro p.
    induction p.
    apply H0.
Defined.


(** Bi-Invertible maps*)
Definition compat_implies_prBiInv
  (A B C D: Type)
  (e: EquivBiInv A B)
  (e':  EquivBiInv C D)
  (a: A -> C)
  (b : B -> D)
  :
    (forall (x : A), (e' o a) x = (b o e) x) -> prBiInv A B C D e e' a b.
Proof.
  revert b.  
  generalize dependent e.
  revert B.
  snrapply equiv_induction_binv.
  generalize dependent e'.
  revert D.
  snrapply equiv_induction_binv.
  simpl.
  intros b K.
  snrapply Build_prBiInv.
  - simpl.
    exact K.
  - intro y.
    simpl.
    exact (K y)^.
  - intro y.
    simpl. 
    exact (K y)^.
  - simpl.
    intro x.
    rewrite ap_idmap.
    rewrite concat_pV.
    reflexivity.
  - simpl. (* induction (H y). causes a bug here *)
    intro y.
    rewrite ap_idmap.
    rewrite concat_Vp.
    reflexivity.
Defined.

Definition compat_iff_prBiInv
  (A B C D: Type)
  (e: EquivBiInv A B)
  (e':  EquivBiInv C D)
  (a: A -> C)
  (b : B -> D)
  :
    (forall (x : A), (e' o a) x = (b o e) x) <-> prBiInv A B C D e e' a b.
Proof.
  split.
    - exact (compat_implies_prBiInv _ _ _ _ _ _ _ _).
    - intro K.
      exact (pe _ _ _ _ _ _ _ _ K).
Defined.


