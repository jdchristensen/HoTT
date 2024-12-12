Require Import Basics.
Require Import Types.Universe Types.Paths Types.Arrow Types.Sigma Cubical.DPath.
Require Import Spaces.Int.
Require Import Spaces.Nat.Core.
Require Import Equiv.BiInv_new.

Module Export IntHIT.
  Section IntHIT.

    Private Inductive IntHIT : Type :=
    | zero_i : IntHIT
    | succ : IntHIT -> IntHIT
    | pred1 : IntHIT -> IntHIT
    | pred2 : IntHIT -> IntHIT.

    Axiom sec : forall (z : IntHIT),
      (pred1 (succ z)) = z.

    Axiom ret : forall (z : IntHIT),
      (succ (pred2 z)) = z.

    (** We define the induction principle. We need to use Fixpoint because it is recursive. *)

    Context {P : IntHIT -> Type} {t0 : P zero_i} {f : forall z : IntHIT, P z -> P (succ z)}
      {g1 : forall z : IntHIT, P z -> P (pred1 z)} {g2 : forall z : IntHIT, P z -> P (pred2 z)}
      {s : forall (z : IntHIT) (t : P z), sec z # (g1 (succ z) (f z t)) = t}
      {r : forall (z : IntHIT) (t : P z), ret z # (f (pred2 z) (g2 z t)) = t}.

    Fixpoint IntHIT_ind
      (x : IntHIT) 
      : P x  
      := match x  with
      | zero_i => fun _ _ => t0
      | succ z => fun _ _ => f z (IntHIT_ind z)
      | pred1 z => fun _ _ => g1 z (IntHIT_ind z)
      | pred2 z => fun _ _ => g2 z (IntHIT_ind z)
      end s r.
      (*We make sure that this is dependent on s and r as well. *)


    (** We define the beta principles for sec and ret. *)
    Axiom IntHIT_ind_beta_sec
     : forall (z: IntHIT),
      (apD IntHIT_ind (sec z)) = s z (IntHIT_ind z).

    Axiom IntHIT_ind_beta_ret
     : forall (z: IntHIT),
      (apD IntHIT_ind (ret z)) = r z (IntHIT_ind z).


  End IntHIT.
End IntHIT.

Definition pred1_is_pred2
  (z : IntHIT)
  : pred1 z = pred2 z
  := (ap pred1 ((ret z) ^)) @ sec (pred2 z).

Definition ret_pred1
    (z: IntHIT)
    : (succ (pred1 z)) = z.
Proof.
  intros.
  exact ((ap succ (pred1_is_pred2 z)) @ (ret z)).
Defined.

  Definition sec_pred2
    (z: IntHIT)
    : (pred2 (succ z)) = z.
Proof.
  intros.
  rewrite (pred1_is_pred2 _)^.
  exact (sec z).
Defined.

Definition IntHIT_ind_hprop
`{P : IntHIT -> Type}
`{h: forall (x : IntHIT), IsHProp (P x)}
(t0 : P zero_i) 
(f : forall z : IntHIT, P z -> P (succ z))
(g1 : forall z : IntHIT, P z -> P (pred1 z))
(g2 : forall z : IntHIT, P z -> P (pred2 z))
(x: IntHIT)
: P x.
Proof.
  srapply IntHIT_ind.
  - exact t0.
  - exact f.
  - exact g1.
  - exact g2.
  - intros z t.
    rapply path_ishprop.
  - intros z t.
    rapply path_ishprop.
Defined.

Definition IntHIT_ind_hprop_pred
`{P : IntHIT -> Type}
`{h: forall (x : IntHIT), IsHProp (P x)}
(t0 : P zero_i) 
(f : forall z : IntHIT, P z -> P (succ z))
(g : forall z : IntHIT, P z -> P (pred1 z))
(x: IntHIT)
: P x.
Proof.
  srapply IntHIT_ind.
  - exact t0.
  - exact f.
  - exact g.
  - intros z t.
    exact ((pred1_is_pred2 z) # (g z) t).
  - intros z t.
    rapply path_ishprop.
  - intros z t.
    rapply path_ishprop.
Defined.


  Definition IntHIT_ind_hprop_succ
`{P : IntHIT -> Type}
`{h: forall (x : IntHIT), IsHProp (P x)}
(t0 : P zero_i) 
(f : forall z : IntHIT, P z <-> P (succ z))
(x: IntHIT)
: P x.
Proof.
  srapply IntHIT_ind.
  - exact t0.
  - intro z.
    destruct (f z).
    exact fst.
  - intros z t.
    destruct (f (pred1 z)).
    exact (snd ((ret_pred1 z)^ # t)).
  - intros z t.
    destruct (f (pred1 z)).
    exact ((pred1_is_pred2 z) # (snd ((ret_pred1 z)^ # t))).
  - intros z t.
    rapply path_ishprop.
  - intros z t.
    rapply path_ishprop.
Defined.
(** The recursion principle.*)
Definition IntHIT_rec
  (P: Type)
  (t0 : P)
  (f :  P -> P)
  (g1 :  P -> P)
  (g2 :  P -> P)
  (s : forall  (t : P ), g1 (f t)= t)
  (r : forall  (t : P ), f (g2 t)= t)
  : IntHIT -> P.
Proof.
  srapply IntHIT_ind.
  - exact t0.
  - intro z.
    exact f.
  - intro z.
    exact g1.
  - intro z.
    exact g2.
  - intros z t.
    refine ((transport_const (sec z) (g1 (f t))) @ (s t)).
  - intros z t.
    refine ((transport_const (ret z) (f (g2 t))) @ (r t)).
Defined.

(** This verison of the recursion principle requires only a biinvertible map. *)
Definition IntHIT_rec_biinv
  (P: Type)
  (t0 : P)
  (f : P -> P)
  `{e: IsBiInv P P f}
  : IntHIT -> P.
Proof.
  srapply IntHIT_ind; cbn beta.
  - exact t0.
  - intro z.
    exact f.
  - intro z.
    exact (retr_biinv f).
  - intro z.
    exact (sect_biinv f).
  - intros z t.
    refine ((transport_const (sec z) (retr_biinv f (f t))) @ ((eissect_biinv f) t)).
  - intros z t.
    refine ((transport_const (ret z) (f ((sect_biinv f) t))) @ ((eisretr_biinv f) t)).
Defined.

(** This verison of the recursion principle requires only a quasiinverse rather than a biinvertible map. *)
Definition IntHIT_rec_qinv
  (P: Type)
  (t0 : P)
  (f : P -> P)
  (g : P -> P)
  (s : forall (t : P ), g (f t)= t)
  (r : forall (t : P ), f (g t)= t)
  : IntHIT -> P.
Proof.
  srapply IntHIT_ind.
  - exact t0.
  - intro z.
    exact f.
  - intro z.
    exact g.
  - intro z.
    exact g.
  - intros z t.
    refine ((transport_const (sec z) (g (f t))) @ (s t)).
  - intros z t.
    refine ((transport_const (ret z) (f (g t))) @ (r t)).
Defined. 


(** This verison of the recursion principle requires only a half-adjoint equivalence.*)
(** Since it is an Instance that biinvertible maps are equivalent to half-adjoint equivalences using type class search one could also use IntHIT_rec_biinv instead.*)
Definition IntHIT_rec_equiv
  (P: Type)
  (t0 : P)
  (f : P -> P)
  `{e: IsEquiv P P f}
  : IntHIT -> P.
Proof.
  exact (IntHIT_rec_biinv _ t0 f (e := (biinv_isequiv _ e))).
Defined.

(** Integers interation*)
Definition IntHIT_iter {A} (f : A -> A) `{!IsEquiv f} (n : IntHIT) (a0: A) : A.
Proof.
  snrapply IntHIT_rec_equiv.
  - exact a0.
  - exact f.
  - exact _.
  - exact n.
Defined.
  
Definition IntHIT_rec_beta_sec
  (P: Type)
  (t0 : P)
  (f :  P -> P)
  (g1 :  P -> P)
  (g2 :  P -> P)
  (s : forall (t : P ), g1 (f t)= t)
  (r : forall (t : P ), f (g2 t)= t)
  : forall (z: IntHIT),
    (let f':= (IntHIT_rec P t0 f g1 g2 s r) in
    ((ap f' (sec z)) = s (f' z))).
Proof.
  intro z.
  unfold IntHIT_rec.
  refine (cancelL _ _ _ _ ).
  refine ((apD_const _ _)^ @ _).
  rapply IntHIT_ind_beta_sec.
Defined.

Definition IntHIT_rec_beta_ret
  (P: Type)
  (t0 : P)
  (f : P -> P)
  (g1 : P -> P)
  (g2 : P -> P)
  (s : forall (t : P ), g1 (f t)= t)
  (r : forall (t : P ), f (g2 t)= t)
  : forall (z: IntHIT),
    (let f':= (IntHIT_rec P t0 f g1 g2 s r) in
    ((ap f' (ret z)) = r (f' z))).
Proof.
  intro z.
  unfold IntHIT_rec.
  refine (cancelL _ _ _ _ ).
  refine ((apD_const _ _)^ @ _).
  rapply IntHIT_ind_beta_ret.
Defined.

(** Successor is biinvertible*)
Global Instance isbiinv_succ
    : IsBiInv succ.
Proof.
  - snrapply Build_IsBiInv.
    + exact pred2.
    + exact pred1.
    + exact ret.
    + exact sec.
Defined.

Definition biinv_IntHIT
    : EquivBiInv IntHIT IntHIT.
Proof.
  exact (Build_EquivBiInv _ _ _ isbiinv_succ).
Defined.

(* * The successor is an equivalence on [IntHIT] *)
Global Instance isequiv_IntHIT_succ : IsEquiv succ
  := isequiv_biinv biinv_IntHIT.

(** The predecessor is an equivalence on [IntHIT] *)
Global Instance isequiv_IntHIT_pred1 : IsEquiv pred1
  := isequiv_inverse succ.

Global Instance isequiv_IntHIT_pred2 : IsEquiv pred2
  := (isequiv_homotopic _ pred1_is_pred2).

Section Uniqueness.

  Context {P : Type} {e: EquivBiInv P P}.

  Local Definition g1 := retr_biinv e.
  Local Definition g2 := sect_biinv e.
  Local Definition s := eissect_biinv e.
  Local Definition r := eisretr_biinv e.
  
  (** We prove a uniqueness principle expressing the universal property of the recursor, up to propositional equality.*)
  Definition uniquenessZ
    (t0 : P)
    (k: IntHIT -> P)
    (p0 : (k zero_i) = t0)
    (pf : forall (z : IntHIT), (e o k) z = (k o succ) z)
    (rec := IntHIT_rec P t0 e g1 g2 s r)
    (compat := compat_implies_prBiInv _ _ _ _ biinv_IntHIT e k k pf)
    : forall (z : IntHIT), k z = rec z.
    Proof.
    snrapply IntHIT_ind. 
    - simpl.
      exact p0.
    - simpl.
      intros z H.
      apply (ap e) in H. 
      exact (((pe _ _ _ _ _ _ _ _ compat z)^) @ H).
    - simpl.
      intros z H.
      apply (ap g1) in H.
      exact (((pr _ _ _ _ _ _ _ _ compat z)^) @ H).
    - intros z H.
      apply (ap g2) in H.
      exact (((ps _ _ _ _ _ _ _ _ compat z)^) @ H).
    - simpl.
      intros z t.
      rewrite transport_paths_FlFr.
      rewrite ap_pp.
      rewrite concat_p_pp.
      rewrite (inv_pp _ _)^.
      rewrite concat_p_pp.
      rewrite ap_V.
      rewrite (inv_pp _ _)^.
      rewrite concat_p_pp.
      rewrite (pre _ _ _ _ _ _ _ _ compat z)^.
      rewrite (concat_p_pp _ _ _)^.
      apply moveR_Vp.
      rewrite (ap_compose _ _ _)^.
      rewrite IntHIT_rec_beta_sec.
      apply (concat_A1p (f := g1 o e)).
    - simpl.
      intros z t.
      rewrite transport_paths_FlFr.
      rewrite ap_pp.
      rewrite concat_p_pp.
      rewrite (inv_pp _ _)^.
      rewrite concat_p_pp.
      rewrite ap_V.
      rewrite (inv_pp _ _)^.
      rewrite concat_p_pp.
      rewrite (pes _ _ _ _ _ _ _ _ compat z)^.
      rewrite (concat_p_pp _ _ _)^.
      apply moveR_Vp.
      rewrite (ap_compose _ _ _)^.
      rewrite IntHIT_rec_beta_ret.
      apply (concat_A1p (f := e o g2)).
  Defined.  
 
(** The following unqueness principle states that if two maps out of [IntHIT] commute with 0 and the successor, then they are equal.*)
Definition uniquenessZ_two_fun_binv
  (k1: IntHIT -> P)
  (k2: IntHIT -> P)
  (p0 : k1 zero_i = k2 zero_i)
  (pf1 : forall (z : IntHIT), (e o k1) z = (k1 o succ) z)
  (pf2 : forall (z : IntHIT), (e o k2) z = (k2 o succ) z)
  : forall (z : IntHIT), k1 z = k2 z.
  Proof.
  intro z.
  exact ((uniquenessZ (k2 zero_i) k1 p0 pf1 z) 
  @ (uniquenessZ (k2 zero_i) k2 idpath pf2 z)^).
Defined.

End Uniqueness.

(** The same uniqueness principle but for half-adjoint equivalences.*)
Definition uniquenessZ_two_fun_equiv 
  {P : Type} 
  (f : P -> P)
  `{e': IsEquiv P P f}
  (k1: IntHIT -> P)
  (k2: IntHIT -> P)
  (p0 : k1 zero_i = k2 zero_i)
  (pf1 : forall (z : IntHIT), (f o k1) z = (k1 o succ) z)
  (pf2 : forall (z : IntHIT), (f o k2) z = (k2 o succ) z)
  : forall (z : IntHIT), k1 z = k2 z.
  Proof.
  exact (uniquenessZ_two_fun_binv (e := Build_EquivBiInv P P _ (biinv_isequiv f e')) k1 k2 p0 pf1 pf2).
Defined.

(** Next we prove that [IntHIT] is equivalent to [Int]*)

Section IntHITEquiv.

  Definition IntHITtoIntIT : IntHIT -> Int.
  Proof.
    srapply IntHIT_rec.
    - exact zero.
    - exact int_succ.
    - exact int_pred.
    - exact int_pred.
    - exact int_succ_pred.
    - exact int_pred_succ.
  Defined.

  Definition IntITtoIntHIT
    (z : Int)
    : IntHIT.
  Proof.
    induction z.
    - exact zero_i.
    - exact (succ IHz).
    - exact (pred1 IHz).
  Defined.

  Definition IntITtoIntHIT_is_rinv
  (z : Int )
  : ((IntHITtoIntIT o IntITtoIntHIT) z) = z.
  Proof.
    induction z as [|[|n] IHz|[|n] IHz].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - apply (ap int_succ) in IHz.
      apply IHz. 
    - simpl.
      reflexivity.
    - simpl.
      apply (ap int_pred) in IHz.
      apply IHz.
  Defined.

  Definition IntITtoIntHIT_comp_succ
    (z: Int)
    : succ (IntITtoIntHIT z) = IntITtoIntHIT ( int_succ z).
    simpl.
    induction z as [|[|n] IHz|[|n] IHz].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      exact (ret_pred1 zero_i).
    - simpl.
      exact ((ret_pred1 _)).
  Defined.

  Definition IntITtoIntHIT_comp_succ'
    (z: IntHIT)
    : succ (IntITtoIntHIT ( IntHITtoIntIT z)) = IntITtoIntHIT ( IntHITtoIntIT (succ z)).
    simpl.
    exact ((IntITtoIntHIT_comp_succ o IntHITtoIntIT) z).
  Defined.

  Definition IntITtoIntHIT_is_linv
  (z : IntHIT )
  : (( IntITtoIntHIT o IntHITtoIntIT) z) = z.
  Proof.
    exact (((uniquenessZ (P := IntHIT) (e := biinv_IntHIT) zero_i (IntITtoIntHIT o IntHITtoIntIT) idpath IntITtoIntHIT_comp_succ') z) 
    @ ((uniquenessZ (P := IntHIT) (e := biinv_IntHIT) zero_i idmap idpath (fun x => idpath)) z)^).
  Defined.

  (** Proof that they are equivalent*)
  Definition isequiv_IntHIT_Int
    : IntHIT <~> Int.
  Proof.
    apply equiv_biinv.
    snrapply Build_EquivBiInv.
      - exact IntHITtoIntIT.
      - srapply Build_IsBiInv.
        * exact IntITtoIntHIT.
        * exact IntITtoIntHIT.
        * exact IntITtoIntHIT_is_rinv.
        * exact IntITtoIntHIT_is_linv.
  Defined.

  (**Therefore [IntHIT] is a set.*)
  Global Instance ishset_IntHIT
    : IsHSet IntHIT.
    Proof.
      snrapply (istrunc_equiv_istrunc _ (equiv_inverse isequiv_IntHIT_Int)).
      exact ishset_int.
    Defined.
  (** We sometimes want to treat the integers as a pointed type with basepoint given by 0. *)
  Global Instance ispointed_IntHIT : IsPointed IntHIT := zero_i.

End IntHITEquiv.

(** Integer Arithmetic using [IntHIT]*)

Section IntegerArithmetic.

  Declare Scope IntHIT_scope.
  Delimit Scope IntHIT_scope with IntHIT.
  Local Open Scope IntHIT_scope.

  (** We define negation by recursion. Negation is defined at this early stage because it will be used in parsing numerals. *)
  Definition IntHIT_neg (x : IntHIT) 
    : IntHIT.
    Proof.
      revert x.
      srapply (IntHIT_rec_equiv _ _ pred1).
      - exact zero_i.
  Defined.

  (** We define addition by recursion on the first argument.*)
  Definition IntHIT_add 
  (x y : IntHIT) 
  : IntHIT.
  Proof.
    revert x.
    snrapply (IntHIT_rec_equiv _ _ succ).
    - exact y.
    - exact isequiv_IntHIT_succ.
  Defined.

  Notation "- x" := (IntHIT_neg x) : IntHIT_scope.

  Notation "z .+1" := (succ z) : IntHIT_scope.
  Notation "z .-1" := (pred1 z) : IntHIT_scope.

  (** We can convert a [nat] to an [IntHIT] by mapping [0] to [zero] and [S n] to [succ n]. Various operations on [nat] are preserved by this function. See the section on conversion functions starting with [int_nat_succ]. *)
  Definition IntHIT_of_nat (n : nat) : IntHIT.
  Proof.
    induction n.
    - exact zero_i.
    - exact (succ IHn).
  Defined.

  (** Printing *)
  (** Here we rely for now on the 'old' integers. This can be maybe improved in the future.*)
  Definition IntHIT_to_number_int  :IntHIT -> Numeral.int := int_to_number_int o IntHITtoIntIT.

  (** Parsing *)
  Definition IntHIT_of_number_int (d : Numeral.int) :=
    match d with
    | Numeral.IntDec (Decimal.Pos d) => IntHIT_of_nat (Nat.of_uint d)
    | Numeral.IntDec (Decimal.Neg d) => IntHIT_neg ( IntHIT_of_nat(Nat.of_uint d))
    | Numeral.IntHex (Hexadecimal.Pos u) => IntHIT_of_nat (Nat.of_hex_uint u)
    | Numeral.IntHex (Hexadecimal.Neg u) => IntHIT_neg (IntHIT_of_nat ((Nat.of_hex_uint u)))
    end.

  Number Notation IntHIT IntHIT_of_number_int IntHIT_to_number_int : IntHIT_scope.

  (** The following function reduces an expression by cancelling succesive successor and predecessor terms. *)
  Definition IntHIT_reduce 
    := IntITtoIntHIT o IntHITtoIntIT.

  (** ** Properties of Operations *)

  (** Negation is involutive. *)
  Definition IntHIT_neg_neg (x: IntHIT): - - x = x.
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (* * Negation is an equivalence. *)
  Global Instance isequiv_int_neg : IsEquiv IntHIT_neg.
  Proof.
    snrapply (isequiv_adjointify IntHIT_neg IntHIT_neg).
    1,2: nrapply IntHIT_neg_neg.
  Defined.

  (** Negation is injective. *)
  Definition isinj_IntHIT_neg (x y : IntHIT) : - x = - y -> x = y
    := equiv_inj IntHIT_neg.

  (** The negation of a successor is the predecessor of the negation. *)
  Definition IntHIT_neg_succ (x : IntHIT) : - succ x = pred1 (-x) := idpath.

  (** The negation of a predecessor is the successor of the negation. *)
  Definition IntHIT_neg_pred (x : IntHIT) : - pred1 x = succ (- x) := idpath.

  (** *** Addition *)

  Infix "+" := IntHIT_add : IntHIT_scope.
  Infix "-" := (fun x y => x + -y) : IntHIT_scope.

  (** Integer addition with zero on the left is the identity by definition. *)
  Definition IntHIT_add_0_l (x : IntHIT) : 0 + x = x := idpath.

  (** Integer addition with zero on the right is the identity. *)
  Definition IntHIT_add_0_r (x : IntHIT) : x + 0 = x.
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (** Adding a successor on the left is the successor of the sum. *)
  Definition IntHIT_add_succ_l (x y : IntHIT) : (succ x) + y = succ (x + y) := idpath.

  (** Adding a predecessor on the left is the predecessor of the sum. *)
  Definition IntHIT_add_pred_l (x y : IntHIT) : (pred1 x) + y = pred1 (x + y) := idpath.

  (** Adding a successor on the right is the successor of the sum. *)
  Definition IntHIT_add_succ_r (x y : IntHIT) : x + (succ y) = succ (x + y).
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (** Adding a predecessor on the right is the predecessor of the sum. *)
  Definition IntHIT_add_pred_r (x y : IntHIT) : x + (pred1 y) = pred1 (x + y).
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv succ); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z.
      rewrite IntHIT_add_succ_l.
      rewrite sec.
      by rewrite ret_pred1.
  Defined.

  (** Integer addition with 1 on the left is the successor. *)
  Definition IntHIT_add_1_l (x : IntHIT) : 1 + x = succ x := idpath.

  (** Integer addition with 1 on the right is the successor. *)
  Definition IntHIT_add_1_r (x : IntHIT) : x + 1 = succ x.
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (** Integer addition is commutative. *)
  Definition IntHIT_add_comm (x y : IntHIT) : x + y = y + x.
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv succ); cbn beta.
    - by rewrite IntHIT_add_0_r.
    - reflexivity.
    - intro z.
      by rewrite IntHIT_add_succ_r.
  Defined. 

  (** Integer addition is associative. *)
  Definition IntHIT_add_assoc (x y z : IntHIT) : x + (y + z) = x + y + z.
  Proof.
    revert x. 
    by srapply (uniquenessZ_two_fun_equiv succ).
  Defined.

  (** Negation is a left inverse with respect to integer addition. *)
  Definition IntHIT_add_neg_l (x : IntHIT) : - x + x = 0.
  Proof.
    revert x. 
    srapply (uniquenessZ_two_fun_equiv idmap); cbn beta.
    - reflexivity.
    - simpl.
      intro s.
      rewrite IntHIT_add_succ_r.
      rewrite sec.
      reflexivity.
    - reflexivity.
  Defined. 

  (** Negation is a right inverse with respect to integer addition. *)
  Definition IntHIT_add_neg_r (x : IntHIT) : x - x = 0.
  Proof.
    unfold "-"; by rewrite IntHIT_add_comm, IntHIT_add_neg_l.
  Defined.

  (** Negation distributes over addition. *)
  Definition IntHIT_neg_add (x y : IntHIT) : - (x + y) = - x - y.
  Proof.
    revert x.
    by srapply (uniquenessZ_two_fun_equiv pred1).
  Defined.

  (** Addition is an equivalence with first argument fixed*)
  Global Instance isequiv_IntHIT_add_l (x : IntHIT): IsEquiv (IntHIT_add x).
  Proof.
    srapply (isequiv_adjointify (IntHIT_add x) (IntHIT_add (-x))).
    - simpl.
      intro y.
      rewrite IntHIT_add_assoc.
      by rewrite IntHIT_add_neg_r.
    - simpl.
      intro y.
      rewrite IntHIT_add_assoc.
      by rewrite IntHIT_add_neg_l.
  Defined.

  (** Addition is an equivalence with second argument fixed*)
  Global Instance isequiv_IntHIT_add_r (y : IntHIT): IsEquiv (fun x => IntHIT_add x y).
  Proof.
    snrapply (isequiv_adjointify (fun x => IntHIT_add x y) (fun x => IntHIT_add x (-y))).
    - simpl.
      intro x.
      rewrite <- IntHIT_add_assoc.
      rewrite IntHIT_add_neg_l.
      by rewrite IntHIT_add_0_r.
    - simpl.
      intro x.
      rewrite <- IntHIT_add_assoc.
      rewrite IntHIT_add_neg_r.
      by rewrite IntHIT_add_0_r.
  Defined.

  (** *** Multiplication *)

  (** We define multiplication by recursion on the first argument. We can only define it at this stage as it depends on the proof that addition is an equivalence. *)
  Definition IntHIT_mul
  (x y : IntHIT) 
  : IntHIT.
  Proof.
    revert x.
    srapply (IntHIT_rec_equiv _ _ (fun z => IntHIT_add z y)).
    - exact 0.
  Defined.

  Infix "*" := IntHIT_mul : IntHIT_scope.

  (** Multiplication with a successor on the left is the sum of the multplication without the successor and the multiplicand which was not a successor. *)
  Definition IntHIT_mul_succ_l (x y : IntHIT) : (succ x) * y = x * y + y := idpath.

  (** Similarly, multiplication with a predecessor on the left is the sum of the multiplication without the predecessor and the negation of the multiplicand which was not a predecessor. *)
  Definition IntHIT_mul_pred_l (x y : IntHIT) : (pred1 x) * y = x * y - y := idpath.

  (** Integer multiplication with zero on the left is zero by definition. *)
  Definition IntHIT_mul_0_l (x : IntHIT) : 0 * x = 0 := idpath.

  (** Integer multiplication with zero on the right is zero. *)
  Definition IntHIT_mul_0_r (x : IntHIT) : x * 0 = 0.
  Proof.
    revert x.
    rapply (uniquenessZ_two_fun_equiv idmap); cbn beta.
    - reflexivity.
    - simpl.
      intro z.
      by rewrite IntHIT_add_0_r.
    - reflexivity.
  Defined.

  (** Integer multiplication with one on the left is the identity. *)
  Definition IntHIT_mul_1_l (x : IntHIT) : 1 * x = x := idpath.

  (** Integer multiplication with one on the right is the identity. *)
  Definition IntHIT_mul_1_r (x : IntHIT) : x * 1 = x.
  Proof.
    revert x.
    rapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x 1)); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z.  
      by rewrite IntHIT_add_1_r.
  Defined.

  (** Multiplying with a negation on the left is the same as negating the product. *)
  Definition IntHIT_mul_neg_l (x y : IntHIT) : - x * y = - (x * y).
  Proof.
    revert x.
    rapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (-y))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro x.
      rewrite IntHIT_mul_succ_l.
      rewrite IntHIT_neg_add.
      reflexivity.
  Defined.

  (** Multiplying with a successor on the right is the sum of the multiplication without the successor and the product of the multiplicand which was not a successor and the multiplicand. *)
  Definition IntHIT_mul_succ_r (x y : IntHIT) : x * (succ y) = x * y + x.
  Proof.
    rewrite IntHIT_add_comm.
    revert x.
    rapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (succ y))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z. 
      rewrite IntHIT_mul_succ_l.
      rewrite IntHIT_add_succ_l.
      rewrite IntHIT_add_succ_r.
      by rewrite IntHIT_add_assoc.
  Defined.

  (** Multiplying with a predecessor on the right is the sum of the multiplication without the predecessor and the product of the multiplicand which was not a predecessor and the negation of the multiplicand which was not a predecessor. *)
  Definition IntHIT_mul_pred_r (x y : IntHIT) : x * (pred1 y) = x * y - x.
  Proof.
    revert x.
    rapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (pred1 y))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z.
      rewrite IntHIT_mul_succ_l.
      rewrite <- IntHIT_add_assoc.
      rewrite (IntHIT_add_comm (-z) _).
      rewrite IntHIT_add_pred_l.
      rewrite <- IntHIT_add_assoc.
      rewrite IntHIT_neg_succ.
      by rewrite (IntHIT_add_pred_r y _).
  Defined.

  (** Integer multiplication is commutative. *)
  Definition IntHIT_mul_comm (x y : IntHIT) : x * y = y * x.
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x y)); cbn beta.
    - by rewrite IntHIT_mul_0_r.
    - reflexivity.
    - intro z.
      by rewrite IntHIT_mul_succ_r.
  Defined.

  (** Multiplying with a negation on the right is the same as negating the product. *)
  Definition IntHIT_mul_neg_r (x y : IntHIT) : x * - y = - (x * y).
  Proof.
    rewrite !(IntHIT_mul_comm x).
    apply IntHIT_mul_neg_l.
  Defined.

  (** Multiplication distributes over addition on the left. *)
  Definition IntHIT_dist_l (x y z : IntHIT) : x * (y + z) = x * y + x * z.
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (y + z))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro x.
      simpl.
      rewrite <- (IntHIT_add_assoc (x*y) y).
      rewrite (IntHIT_add_comm y (x*z + z)).
      rewrite <- (IntHIT_add_assoc _ z y).
      rewrite (IntHIT_add_comm z y).
      by rewrite 3 IntHIT_add_assoc.
  Defined.

  (** Multiplication distributes over addition on the right. *)
  Definition IntHIT_dist_r (x y z : IntHIT) : (x + y) * z = x * z + y * z.
  Proof.
    by rewrite IntHIT_mul_comm, IntHIT_dist_l, !(IntHIT_mul_comm z).
  Defined.

  (** Multiplication is associative. *)
  Definition IntHIT_mul_assoc (x y z : IntHIT) : x * (y * z) = x * y * z.
  Proof.
    revert x.
    srapply (uniquenessZ_two_fun_equiv (fun x => IntHIT_add x (y * z))); cbn beta.
    - reflexivity.
    - reflexivity.
    - simpl.
      intro x.
      by rewrite IntHIT_dist_r.
  Defined.

  (** This is a shorter proof of linv, but it requires that we already know that IntHIT is as set. This might be useful in the future, if we can show that [IntHIT] a set independently of its equivalence to [Int]. *)
  Definition IntITtoIntHIT_is_linv'
  (z : IntHIT )
  : (( IntITtoIntHIT o IntHITtoIntIT) z) = z.
  Proof.
    srapply (uniquenessZ_two_fun_equiv succ).
    - reflexivity.
    - simpl.
      exact IntITtoIntHIT_comp_succ'.
    - reflexivity. 
  Defined.

End IntegerArithmetic.
