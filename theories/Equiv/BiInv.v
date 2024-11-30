Require Import Basics Types.Prod Types.Equiv Types.Sigma Types.Universe.

Local Open Scope path_scope.
Generalizable Variables A B f.

(** * Bi-invertible maps *)

(** A map is "bi-invertible" if it has both a section and a retraction, not necessarily the same.  This definition of equivalence was proposed by Andre Joyal. *)

Definition BiInv `(f : A -> B) : Type
  := {g : B -> A & g o f == idmap} * {h : B -> A & f o h == idmap}.

(** It seems that the easiest way to show that bi-invertibility is equivalent to being an equivalence is also to show that both are h-props and that they are logically equivalent. *)

Definition isequiv_biinv `(f : A -> B)
  : BiInv f -> IsEquiv f.
Proof.
  intros [[g s] [h r]].
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
  intros bif; pose (fe := isequiv_biinv f bif).
  apply @contr_prod.
  (* For this, we've done all the work already. *)
  - by apply contr_retr_equiv.
  - by apply contr_sect_equiv.
Defined.

Definition equiv_biinv_isequiv `{Funext} `(f : A -> B)
  : BiInv f <~> IsEquiv f.
Proof.
  apply equiv_iff_hprop_uncurried, iff_biinv_isequiv.
Defined.


(** These are some projections *)
Definition ret_binv `{f : A -> B}
  : BiInv f ->  (B -> A).
  intro X.
  exact (pr1 (fst X)).
Defined.

Definition sec_binv `{f : A -> B}
  : BiInv f ->  (B -> A).
  intro X.
  exact (pr1 (snd X)).
Defined.

Definition isret_binv `{f : A -> B}
  : forall (e: BiInv f), f o (sec_binv e)   == idmap.
  intro.
  simpl.
  exact (pr2 (snd e)).
Defined.

Definition issec_binv `{f : A -> B}
  : forall (e: BiInv f), (ret_binv e) o f   == idmap.
  intro.
  simpl.
  exact (pr2 (fst e)).
Defined.

(** A record summing over all bi-invertible maps*)

Record EquivBiInv A B := {
  equiv_fun_binv :> A -> B ;
  equiv_isequiv_binv :> BiInv equiv_fun_binv
}.

Definition issig_equivbiinv (A B : Type)
  : {f : A -> B & BiInv f} <~> EquivBiInv A B.
Proof.
  issig.
Defined.

(* Some lemmas to send equivalences and biinvertible maps back and forth.*)

Definition isequiv_biinv_record A B
  : EquivBiInv A B -> A <~> B.
Proof.
  intros [f e].
  exact (Build_Equiv A B f (isequiv_biinv f e)).
Defined.

Definition biinv_isequiv_record A B
  :  A <~> B -> EquivBiInv A B.
Proof.
  intros [f e].
  exact (Build_EquivBiInv A B f (biinv_isequiv f e)).
Defined.

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
  snrapply (Build_EquivBiInv A A).
  - exact idmap.
  -
    snrapply pair.
    -- snrapply exist.
       --- exact idmap.
       --- simpl.
           reflexivity. 
    -- snrapply exist.
       --- exact idmap.
       --- simpl.
           reflexivity.
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


(* Generalizable Variables C D. *)

Record prBiInv A B C D (e: EquivBiInv A B) (e' : EquivBiInv C D) (a: A -> C) (b: B -> D)
  := {
  pe : forall (x : A), (e' o a) x = (b o e) x;
  pg : forall (y : B), ((ret_binv e') o b) y = (a o (ret_binv e)) y;
  ph : forall (y : B), ((sec_binv e') o b) y = (a o (sec_binv e )) y;
  ps : forall (x: A), (issec_binv e' (a x)) = ((ap (ret_binv e') (pe x)) @ (pg (e x)) @ (ap a (issec_binv e x) ));
  pr : forall (y: B), (isret_binv e'(b y)) = ((ap e' (ph y)) @ (pe (sec_binv e y)) @ (ap b (isret_binv e y) ));
}.


Definition compat_implies_prBiInv'
  (A B C D: Type)
  (e: EquivBiInv A B)
  (e':  EquivBiInv C D)
  (a: A -> C)
  (b : B -> D)
  (s := issec_binv e)
  (r := isret_binv e)
  (p1 := ret_binv e)
  (p2 := sec_binv e)
  (g1 := ret_binv e')
  (g2 := sec_binv e')
  (s' := issec_binv e')
  (r' := isret_binv e')
  (* (p2_is_p1 z := ( (s (p2 z))^ @ (ap p1 (r z)))) *)
  (* (g2_is_g1 z := ( (s' (g2 z))^ @ (ap g1 (r z)))) *)
  : (forall (x : A), (e' o a) x = (b o e) x) -> prBiInv A B C D e e' a b.
Proof.
  intro pf.
  srapply Build_prBiInv.
  - exact pf.
  - intro z.
    exact ((ap (g1 o b) (r z))^ @ (ap g1 (pf (p2 z)))^ @ (s' (a (p2 z)))
          @ (ap a ((s (p2 z))^ @ (ap p1 (r z))))).
  - intro z. 
    exact (((s' (g2 (b z)))^ @ (ap g1 (r' (b z)))) @ (ap (g1 o b) (r z))^ 
          @ (ap g1 (pf (p2 z)))^ @ (s' (a (p2 z)))).
  - intro x.
    simpl.
Admitted.



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


