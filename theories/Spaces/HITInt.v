Require Import HoTT.Basics Types.Paths Spaces.Nat.Core Spaces.SInt Equiv.BiInv.

(** * The integers, defined as a HIT *)

(** Following "The integers as a higher inductive type" by Scoccola and Altenkirch, we define the integers as a higher inductive type.  Morally it is the free pointed type with a biinvertible self-map. *)

Set Universe Minimization ToSet.

Module Export IntHIT.
  Section IntHIT.

    (** Here we are modeling the HIT which has a point [zero_i] and a successor map [succ] which is a biinvertible equivalence.  [pred] and [succ_sect] are its left and right inverses. *)

    Private Inductive IntHIT : Type0 :=
    | zero_i : IntHIT
    | succ : IntHIT -> IntHIT
    | pred : IntHIT -> IntHIT
    | succ_sect : IntHIT -> IntHIT.

    Axiom succ_is_sect : pred o succ == idmap.

    Axiom succ_is_retr : succ o succ_sect == idmap.

    Context {P : IntHIT -> Type} (t0 : P zero_i) (e : forall z : IntHIT, P z -> P (succ z))
      (r : forall z : IntHIT, P z -> P (pred z)) (s : forall z : IntHIT, P z -> P (succ_sect z))
      (re : forall (z : IntHIT) (t : P z), succ_is_sect z # (r (succ z) (e z t)) = t)
      (es : forall (z : IntHIT) (t : P z), succ_is_retr z # (e (succ_sect z) (s z t)) = t).

    Fixpoint IntHIT_ind (z : IntHIT) : P z
      := match z with
      | zero_i => fun _ _ => t0
      | succ z => fun _ _ => e z (IntHIT_ind z)
      | pred z => fun _ _ => r z (IntHIT_ind z)
      | succ_sect z => fun _ _ => s z (IntHIT_ind z)
      end re es.
      (** We make sure that this depends on [re] and [es] as well. *)

    (** The beta principles for [IntHIT_ind] on [succ_is_sect] and [succ_is_retr]. *)
    Axiom IntHIT_ind_beta_succ_is_sect
      : forall (z : IntHIT), apD IntHIT_ind (succ_is_sect z) = re z (IntHIT_ind z).

    Axiom IntHIT_ind_beta_succ_is_retr
      : forall (z : IntHIT), apD IntHIT_ind (succ_is_retr z) = es z (IntHIT_ind z).

  End IntHIT.
End IntHIT.

(** Successor is biinvertible.  It follows from typeclass inference that it is an equivalence. *)
#[export] Instance isbiinv_IntHIT_succ : IsBiInv succ
  := Build_IsBiInv _ _ _ succ_sect pred succ_is_retr succ_is_sect.

Definition biinv_IntHIT_succ : BiInv IntHIT IntHIT
  := Build_BiInv _ _ succ _.

(** The predecessor is an equivalence on [IntHIT]. *)
#[export] Instance isequiv_IntHIT_pred : IsEquiv pred
  := isequiv_isbiinv_retr succ.

Definition IntHIT_ind_equiv {P : IntHIT -> Type} (t0 : P zero_i)
  (e : forall z : IntHIT, P z -> P (succ z)) {iseq : forall z, IsEquiv (e z)}
  : forall z, P z.
Proof.
  snapply (IntHIT_ind t0 e).
  - intro z.
    exact ((e (pred z))^-1 o transport P (retr_is_sect_isbiinv biinv_IntHIT_succ z)^).
  - intro z.
    exact ((e (succ_sect z))^-1 o transport P (succ_is_retr z)^).
  - intros z p; cbn beta.
    lhs_V napply (ap_transport _ (fun z => (e z)^-1)).
    lhs napply (ap (e z)^-1).
    { lhs napply transport_compose.
      symmetry; napply transport_pp. }
    unfold retr_is_sect_isbiinv.
    (* In the next line we use that our chosen proof of [retr_is_sect_isbiinv] satisfies the adjoint law. *)
    rewrite (eisadj succ); cbn.
    rewrite concat_Vp; cbn.
    apply eissect.
  - intros z p; cbn beta.
    rewrite eisretr.
    apply transport_pV.
Defined.

Definition IntHIT_ind_hprop {P : IntHIT -> Type} `{forall z, IsHProp (P z)}
  (t0 : P zero_i) (f : forall z : IntHIT, P z -> P (succ z))
  (g : forall z : IntHIT, P z -> P (pred z))
  : forall z, P z.
Proof.
  snapply (IntHIT_ind t0 f g).
  - intros z t.
    exact ((sect_retr_homotopic_isbiinv succ z)^ # (g z) t).
  - intros z t.
    rapply path_ishprop.
  - intros z t.
    rapply path_ishprop.
Defined.

Definition IntHIT_ind_hprop_iff {P : IntHIT -> Type} `{forall z, IsHProp (P z)}
  (t0 : P zero_i) (f : forall z : IntHIT, P z <-> P (succ z))
  : forall z, P z.
Proof.
  srapply (IntHIT_ind_hprop t0).
  - intro z.  exact (fst (f z)).
  - equiv_intro succ z.
    refine (_ o snd (f z)).
    exact (transport P (succ_is_sect z)^).
Defined.

Section RecursionPrinciple.

  Context {P : Type} (t0 : P) (f : P -> P) (g1 g2 : P -> P)
    (s : g1 o f == idmap) (r : f o g2 == idmap).

  (** The recursion principle. *)
  Definition IntHIT_rec : IntHIT -> P.
  Proof.
    snapply (IntHIT_ind t0 (fun _ => f) (fun _ => g1) (fun _ => g2)).
    all: intros z t; cbn.
    all: lhs napply transport_const.
    - apply s.
    - apply r.
  Defined.

  Definition IntHIT_rec_beta_succ_is_sect
    : forall z, ap IntHIT_rec (succ_is_sect z) = s (IntHIT_rec z).
  Proof.
    intro z.
    napply (cancelL (transport_const (succ_is_sect z) _)).
    lhs_V napply apD_const.
    napply IntHIT_ind_beta_succ_is_sect.
  Defined.

  Definition IntHIT_rec_beta_succ_is_retr
    : forall z, ap IntHIT_rec (succ_is_retr z) = r (IntHIT_rec z).
  Proof.
    intro z.
    napply (cancelL (transport_const (succ_is_retr z) _)).
    lhs_V napply apD_const.
    napply IntHIT_ind_beta_succ_is_retr.
  Defined.

End RecursionPrinciple.

(** The recursion principle phrased using a biinvertible map. *)
Definition IntHIT_rec_biinv {P : Type} (t0 : P) (f : P -> P) `{IsBiInv P P f}
  : IntHIT -> P
  := IntHIT_rec t0 f (retr_biinv f) (sect_biinv f) (eissect_biinv f) (eisretr_biinv f).

(** The recursion principle phrased using a half-adjoint equivalence. *)
Definition IntHIT_rec_equiv {P : Type} (t0 : P) (f : P -> P) `{IsEquiv P P f}
  : IntHIT -> P
  := @IntHIT_rec_biinv P t0 f (isbiinv_isequiv _ _).

(** We define equivalence iteration. *)
Definition IntHIT_iter {A} (f : A -> A) `{!IsEquiv f} (n : IntHIT) (a0 : A) : A
  := IntHIT_rec_equiv a0 f n.

Section Uniqueness.

  Context {P : Type} {e : BiInv P P}.

  (** The following uniqueness principle states that if two maps out of [IntHIT] agree on 0 and commute with the successor, then they are homotopic. *)
  Definition IntHIT_homotopic_two_fun_biinv (k1 : IntHIT -> P) (k2 : IntHIT -> P)
    (p0 : k1 zero_i = k2 zero_i) (pf1 : k1 o succ == e o k1) (pf2 : k2 o succ == e o k2)
    : k1 == k2.
  Proof.
    snapply IntHIT_ind_equiv; cbn beta.
    - exact p0.
    - intro z.
      exact (equiv_concat_l (pf1 z) _ oE equiv_concat_r (pf2 z)^ _ oE equiv_ap e _ _).
    - exact _.
  Defined.

  (** As a special case, we can characterize the recursor. *)
  Definition IntHIT_homotopic (t0 : P) (k : IntHIT -> P)
    (p0 : k zero_i = t0) (pf : k o succ == e o k)
    (rec := IntHIT_rec_biinv t0 e)
    : k == rec
    := IntHIT_homotopic_two_fun_biinv k rec p0 pf (fun _ => idpath).

End Uniqueness.

(** The same uniqueness principle but for half-adjoint equivalences. *)
Definition IntHIT_homotopic_two_fun_equiv {P : Type} (f : P -> P)
  {e' : IsEquiv f} (k1 : IntHIT -> P) (k2 : IntHIT -> P)
  (p0 : k1 zero_i = k2 zero_i) (pf1 : k1 o succ == f o k1)
  (pf2 : k2 o succ == f o k2)
  : forall (z : IntHIT), k1 z = k2 z
  := IntHIT_homotopic_two_fun_biinv (e := Build_BiInv P P _ (isbiinv_isequiv f e')) k1 k2 p0 pf1 pf2.

(** Next we prove that [IntHIT] is equivalent to [SInt]. *)

Section IntHITEquiv.

  Definition IntHITtoIntIT : IntHIT -> SInt
    := IntHIT_rec zero int_succ int_pred int_pred int_succ_pred int_pred_succ.

  Definition IntITtoIntHIT (z : SInt) : IntHIT.
  Proof.
    induction z as [|n IHz|n IHz].
    - exact zero_i.
    - exact (succ IHz).
    - exact (pred IHz).
  Defined.

  Definition IntITtoIntHIT_is_rinv (z : SInt)
    : (IntHITtoIntIT o IntITtoIntHIT) z = z.
  Proof.
    induction z as [|[|n] IHz|[|n] IHz].
    1, 2, 4: reflexivity.
    - exact (ap int_succ IHz).
    - exact (ap int_pred IHz).
  Defined.

  Definition IntITtoIntHIT_comp_succ (z : SInt)
    : IntITtoIntHIT (int_succ z) = succ (IntITtoIntHIT z).
  Proof.
    induction z as [|[|n] IHz|[|n] IHz].
    1-3: reflexivity.
    all: symmetry; exact (retr_is_sect_isbiinv succ _).
  Defined.

  Definition IntITtoIntHIT_comp_succ' (z : IntHIT)
    : IntITtoIntHIT (IntHITtoIntIT (succ z)) = succ (IntITtoIntHIT (IntHITtoIntIT z))
    := IntITtoIntHIT_comp_succ (IntHITtoIntIT z).

  Definition IntITtoIntHIT_is_linv (z : IntHIT)
    : (IntITtoIntHIT o IntHITtoIntIT) z = z.
  Proof.
    exact (IntHIT_homotopic (e := biinv_IntHIT_succ) zero_i (IntITtoIntHIT o IntHITtoIntIT) idpath IntITtoIntHIT_comp_succ' z
             @ (IntHIT_homotopic (e := biinv_IntHIT_succ) zero_i idmap idpath (fun x => idpath) z)^).
  Defined.

  (** [IntITtoIntHIT] is biinvertible.  It follows from typeclass inference that it is an equivalence and that [SInt] and [IntHIT] are equivalent. *)
  #[export] Instance isbiinv_IntITtoIntHIT
    : IsBiInv IntITtoIntHIT
    := Build_IsBiInv _ _ _ _ _ IntITtoIntHIT_is_linv IntITtoIntHIT_is_rinv.

  (** Since [SInt] is a set, therefore also [IntHIT] is a set. *)
  #[export] Instance ishset_IntHIT
    : IsHSet IntHIT
    := istrunc_isequiv_istrunc SInt _.

  (** We sometimes want to treat the integers as a pointed type with basepoint given by 0. *)
  #[export] Instance ispointed_IntHIT : IsPointed IntHIT := zero_i.

End IntHITEquiv.

(** * Integer Arithmetic using [IntHIT] *)

Section IntegerArithmetic.

  Declare Scope IntHIT_scope.
  Delimit Scope IntHIT_scope with IntHIT.
  Local Open Scope IntHIT_scope.

  Notation "z .+1" := (succ z) : IntHIT_scope.
  Notation "z .-1" := (pred z) : IntHIT_scope.

  (** We define negation by recursion.  Negation is defined at this early stage because it will be used in parsing numerals. *)
  Definition IntHIT_neg (z : IntHIT) : IntHIT
    := IntHIT_rec_equiv zero_i pred z.

  Notation "- z" := (IntHIT_neg z) : IntHIT_scope.

  (** We define addition by recursion on the first argument. *)
  Definition IntHIT_add (x y : IntHIT) : IntHIT
    := IntHIT_rec_equiv y succ x.

  (** We can convert a [nat] to an [IntHIT] by mapping [0] to [zero] and [S n] to [succ n].  Various operations on [nat] are preserved by this function. See the section on conversion functions starting with [int_nat_succ]. *)
  Definition IntHIT_of_nat (n : nat) : IntHIT
    := nat_iter n succ zero_i.

  (** Printing *)
  (** Here we rely for now on the 'old' integers. This can be maybe improved in the future. *)
  Definition IntHIT_to_number_int : IntHIT -> Numeral.int := int_to_number_int o IntHITtoIntIT.

  (** Parsing *)
  Definition IntHIT_of_number_int (d : Numeral.int) :=
    match d with
    | Numeral.IntDec (Decimal.Pos d) => IntHIT_of_nat (Nat.of_uint d)
    | Numeral.IntDec (Decimal.Neg d) => IntHIT_neg (IntHIT_of_nat (Nat.of_uint d))
    | Numeral.IntHex (Hexadecimal.Pos u) => IntHIT_of_nat (Nat.of_hex_uint u)
    | Numeral.IntHex (Hexadecimal.Neg u) => IntHIT_neg (IntHIT_of_nat (Nat.of_hex_uint u))
    end.

  Number Notation IntHIT IntHIT_of_number_int IntHIT_to_number_int : IntHIT_scope.

  (** The following function reduces an integer expression by cancelling succesive successor and predecessor terms. *)
  Definition IntHIT_reduce := IntITtoIntHIT o IntHITtoIntIT.

  (** ** Properties of Operations *)

  (** Negation is involutive. *)
  Definition IntHIT_neg_neg (z : IntHIT): - - z = z.
  Proof.
    revert z.
    by srapply (IntHIT_homotopic_two_fun_equiv succ).
  Defined.

  (* * Negation is an equivalence. *)
  #[export] Instance isequiv_int_neg : IsEquiv IntHIT_neg.
  Proof.
    snapply (isequiv_adjointify IntHIT_neg IntHIT_neg).
    1,2: napply IntHIT_neg_neg.
  Defined.

  (** Negation is injective. *)
  Definition isinj_IntHIT_neg (x y : IntHIT) : - x = - y -> x = y
    := equiv_inj IntHIT_neg.

  (** The negation of a successor is the predecessor of the negation. *)
  Definition IntHIT_neg_succ (z : IntHIT) : - succ z = pred (-z)
    := idpath.

  (** The negation of a predecessor is the successor of the negation. *)
  Definition IntHIT_neg_pred (z : IntHIT) : - pred z = succ (- z)
    := idpath.

  (** *** Addition *)

  Infix "+" := IntHIT_add : IntHIT_scope.
  Infix "-" := (fun x y => x + -y) : IntHIT_scope.

  (** Integer addition with zero on the left is the identity by definition. *)
  Definition IntHIT_add_0_l (z : IntHIT) : 0 + z = z
    := idpath.

  (** Integer addition with zero on the right is the identity. *)
  Definition IntHIT_add_0_r (z : IntHIT) : z + 0 = z.
  Proof.
    revert z.
    by srapply (IntHIT_homotopic_two_fun_equiv succ).
  Defined.

  (** Adding a successor on the left is the successor of the sum. *)
  Definition IntHIT_add_succ_l (x y : IntHIT) : (succ x) + y = succ (x + y)
    := idpath.

  (** Adding a predecessor on the left is the predecessor of the sum. *)
  Definition IntHIT_add_pred_l (x y : IntHIT) : (pred x) + y = pred (x + y)
    := idpath.

  (** Adding a successor on the right is the successor of the sum. *)
  Definition IntHIT_add_succ_r (x y : IntHIT) : x + (succ y) = succ (x + y).
  Proof.
    revert x.
    by srapply (IntHIT_homotopic_two_fun_equiv succ).
  Defined.

  (** Adding a predecessor on the right is the predecessor of the sum. *)
  Definition IntHIT_add_pred_r (x y : IntHIT) : x + (pred y) = pred (x + y).
  Proof.
    revert x.
    srapply (IntHIT_homotopic_two_fun_equiv succ); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z.
      simpl.
      rewrite succ_is_sect.
      exact (retr_is_sect_isbiinv succ _)^.
  Defined.

  (** Integer addition with 1 on the left is the successor. *)
  Definition IntHIT_add_1_l (z : IntHIT) : 1 + z = succ z
    := idpath.

  (** Integer addition with 1 on the right is the successor. *)
  Definition IntHIT_add_1_r (z : IntHIT) : z + 1 = succ z.
  Proof.
    revert z.
    by srapply (IntHIT_homotopic_two_fun_equiv succ).
  Defined.

  (** Integer addition is commutative. *)
  Definition IntHIT_add_comm (x y : IntHIT) : x + y = y + x.
  Proof.
    revert x.
    srapply (IntHIT_homotopic_two_fun_equiv succ); cbn beta.
    - by rewrite IntHIT_add_0_r.
    - reflexivity.
    - intro z.
      by rewrite IntHIT_add_succ_r.
  Defined.

  (** Integer addition is associative. *)
  Definition IntHIT_add_assoc (x y z : IntHIT) : x + (y + z) = x + y + z.
  Proof.
    revert x.
    by srapply (IntHIT_homotopic_two_fun_equiv succ).
  Defined.

  (** Negation is a left inverse with respect to integer addition. *)
  Definition IntHIT_add_neg_l (z : IntHIT) : - z + z = 0.
  Proof.
    revert z.
    srapply (IntHIT_homotopic_two_fun_equiv idmap); cbn beta.
    - reflexivity.
    - simpl; intro s.
      rewrite IntHIT_add_succ_r.
      apply succ_is_sect.
    - reflexivity.
  Defined.

  (** Negation is a right inverse with respect to integer addition. *)
  Definition IntHIT_add_neg_r (z : IntHIT) : z - z = 0.
  Proof.
    unfold "-"; by rewrite IntHIT_add_comm, IntHIT_add_neg_l.
  Defined.

  (** Negation distributes over addition. *)
  Definition IntHIT_neg_add (x y : IntHIT) : - (x + y) = - x - y.
  Proof.
    revert x.
    by srapply (IntHIT_homotopic_two_fun_equiv pred).
  Defined.

  (** Addition is an equivalence with first argument fixed. *)
  #[export] Instance isequiv_IntHIT_add_l (x : IntHIT): IsEquiv (IntHIT_add x).
  Proof.
    srapply (isequiv_adjointify _ (IntHIT_add (-x))).
    all: simpl; intro y.
    all: lhs napply IntHIT_add_assoc.
    - by rewrite IntHIT_add_neg_r.
    - by rewrite IntHIT_add_neg_l.
  Defined.

  (** Addition is an equivalence with second argument fixed.  This also follows from the previous result and [IntHIT_add_comm], but this proof computes better. *)
  #[export] Instance isequiv_IntHIT_add_r (y : IntHIT) : IsEquiv (fun x => IntHIT_add x y).
  Proof.
    snapply (isequiv_adjointify _ (fun x => IntHIT_add x (-y))).
    all: simpl; intro x.
    all: lhs_V napply IntHIT_add_assoc.
    - rewrite IntHIT_add_neg_l.
      apply IntHIT_add_0_r.
    - rewrite IntHIT_add_neg_r.
      apply IntHIT_add_0_r.
  Defined.

  (** *** Multiplication *)

  (** We define multiplication by recursion on the first argument.  We can only define it at this stage as it depends on the proof that addition is an equivalence. *)
  Definition IntHIT_mul (x y : IntHIT) : IntHIT
    := IntHIT_iter (fun z => IntHIT_add z y) x 0.

  Infix "*" := IntHIT_mul : IntHIT_scope.

  (** Multiplication with a successor on the left is the sum of the multplication without the successor and the multiplicand which was not a successor. *)
  Definition IntHIT_mul_succ_l (x y : IntHIT) : (succ x) * y = x * y + y
    := idpath.

  (** Similarly, multiplication with a predecessor on the left is the sum of the multiplication without the predecessor and the negation of the multiplicand which was not a predecessor. *)
  Definition IntHIT_mul_pred_l (x y : IntHIT) : (pred x) * y = x * y - y
    := idpath.

  (** Integer multiplication with zero on the left is zero by definition. *)
  Definition IntHIT_mul_0_l (z : IntHIT) : 0 * z = 0
    := idpath.

  (** Integer multiplication with zero on the right is zero. *)
  Definition IntHIT_mul_0_r (z : IntHIT) : z * 0 = 0.
  Proof.
    revert z.
    rapply (IntHIT_homotopic_two_fun_equiv idmap); cbn beta.
    - reflexivity.
    - simpl.
      intro z.
      by rewrite IntHIT_add_0_r.
    - reflexivity.
  Defined.

  (** Integer multiplication with one on the left is the identity. *)
  Definition IntHIT_mul_1_l (z : IntHIT) : 1 * z = z
    := idpath.

  (** Integer multiplication with one on the right is the identity. *)
  Definition IntHIT_mul_1_r (z : IntHIT) : z * 1 = z.
  Proof.
    revert z.
    rapply (IntHIT_homotopic_two_fun_equiv (fun z => IntHIT_add z 1)); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z.
      by rewrite IntHIT_add_1_r.
  Defined.

  (** Integer multiplication with -1 on the left is negation. *)
  Definition IntHIT_mul_neg1_l (z : IntHIT) : (-1) * z = - z
    := idpath.

  (** Multiplying with a negation on the left is the same as negating the product. *)
  Definition IntHIT_mul_neg_l (x y : IntHIT) : - x * y = - (x * y).
  Proof.
    revert x.
    rapply (IntHIT_homotopic_two_fun_equiv (fun x => IntHIT_add x (-y))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro x; simpl.
      rewrite IntHIT_neg_add.
      reflexivity.
  Defined.

  (** Multiplying with a successor on the right is the sum of the multiplication without the successor and the product of the multiplicand which was not a successor and the multiplicand. *)
  Definition IntHIT_mul_succ_r (x y : IntHIT) : x * (succ y) = x + x * y.
  Proof.
    revert x.
    rapply (IntHIT_homotopic_two_fun_equiv (fun x => IntHIT_add x (succ y))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z; simpl.
      rewrite IntHIT_add_succ_r.
      by rewrite IntHIT_add_assoc.
  Defined.

  (** Multiplying with a predecessor on the right is the sum of the multiplication without the predecessor and the product of the multiplicand which was not a predecessor and the negation of the multiplicand which was not a predecessor. *)
  Definition IntHIT_mul_pred_r (x y : IntHIT) : x * (pred y) = x * y - x.
  Proof.
    revert x.
    rapply (IntHIT_homotopic_two_fun_equiv (fun x => IntHIT_add x (pred y))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro z.
      rewrite IntHIT_mul_succ_l.
      rewrite <- IntHIT_add_assoc.
      simpl.
      rewrite (IntHIT_add_comm y _).
      rewrite IntHIT_add_pred_l.
      rewrite <- IntHIT_add_assoc.
      by rewrite (IntHIT_add_pred_r _ y).
  Defined.

  (** Integer multiplication is commutative. *)
  Definition IntHIT_mul_comm (x y : IntHIT) : x * y = y * x.
  Proof.
    revert x.
    srapply (IntHIT_homotopic_two_fun_equiv (fun x => IntHIT_add x y)); cbn beta.
    - symmetry; apply IntHIT_mul_0_r.
    - reflexivity.
    - intro z.
      rewrite IntHIT_add_comm.
      apply IntHIT_mul_succ_r.
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
    srapply (IntHIT_homotopic_two_fun_equiv (fun x => IntHIT_add x (y + z))); cbn beta.
    - reflexivity.
    - reflexivity.
    - intro x.
      simpl.
      rewrite <- (IntHIT_add_assoc (x*y) y).
      rewrite (IntHIT_add_comm y (x*z + z)).
      rewrite <- (IntHIT_add_assoc _ z y).
      rewrite (IntHIT_add_comm z y).
      by rewrite (IntHIT_add_assoc (x*y) _ _).
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
    srapply (IntHIT_homotopic_two_fun_equiv (fun x => IntHIT_add x (y * z))); cbn beta.
    - reflexivity.
    - reflexivity.
    - simpl.
      intro x.
      by rewrite IntHIT_dist_r.
  Defined.

  (** This is a shorter proof of [IntITtoIntHIT_is_linv], but it requires that we already know that [IntHIT] is as set.  This might be useful in the future, if we can show that [IntHIT] a set independently of its equivalence to [SInt]. *)
  Definition IntITtoIntHIT_is_linv' (z : IntHIT)
  : (IntITtoIntHIT o IntHITtoIntIT) z = z.
  Proof.
    srapply (IntHIT_homotopic_two_fun_equiv succ).
    - reflexivity.
    - simpl.
      exact IntITtoIntHIT_comp_succ'.
    - reflexivity.
  Defined.

End IntegerArithmetic.
