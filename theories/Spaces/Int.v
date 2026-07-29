Require Import HoTT.Basics Types.Paths Spaces.Nat.Core Spaces.SInt Equiv.BiInv Types.Paths Types.Universe.

Require Export Equiv.BiInv.

(** * The integers, defined as a HIT *)

(** Following "The integers as a higher inductive type" by Scoccola and Altenkirch, we define the integers as a higher inductive type.  Morally it is the free pointed type with a biinvertible self-map. *)

Set Universe Minimization ToSet.

Declare Scope int_scope.
Delimit Scope int_scope with int.
Local Open Scope int_scope.

(** ** The definition of [Int] *)

Module Export Int.
  Section Int.

    (** Here we are modeling the HIT which has a point [zero_i] and a successor map [succ] which is a biinvertible equivalence.  [pred] and [succ_sect] are its left and right inverses. *)

    Private Inductive Int : Type0 :=
    | zero_i : Int
    | succ : Int -> Int
    | pred : Int -> Int
    | succ_sect : Int -> Int.

    Axiom succ_is_sect : pred o succ == idmap.

    Axiom succ_is_retr : succ o succ_sect == idmap.

    Context {P : Int -> Type} (t0 : P zero_i) (e : forall z : Int, P z -> P (succ z))
      (r : forall z : Int, P z -> P (pred z)) (s : forall z : Int, P z -> P (succ_sect z))
      (re : forall (z : Int) (t : P z), succ_is_sect z # (r (succ z) (e z t)) = t)
      (es : forall (z : Int) (t : P z), succ_is_retr z # (e (succ_sect z) (s z t)) = t).

    Fixpoint int_ind (z : Int) : P z
      := match z with
      | zero_i => fun _ _ => t0
      | succ z => fun _ _ => e z (int_ind z)
      | pred z => fun _ _ => r z (int_ind z)
      | succ_sect z => fun _ _ => s z (int_ind z)
      end re es.
      (** We make sure that this depends on [re] and [es] as well. *)

    (** The beta principles for [int_ind] on [succ_is_sect] and [succ_is_retr]. *)
    Axiom int_ind_beta_succ_is_sect
      : forall (z : Int), apD int_ind (succ_is_sect z) = re z (int_ind z).

    Axiom int_ind_beta_succ_is_retr
      : forall (z : Int), apD int_ind (succ_is_retr z) = es z (int_ind z).

  End Int.
End Int.

(** We sometimes want to treat the integers as a pointed type with basepoint given by 0. *)
#[export] Instance ispointed_int : IsPointed Int := zero_i.

(** Successor is biinvertible.  It follows from typeclass inference that it is an equivalence. *)
#[export] Instance isbiinv_int_succ : IsBiInv succ
  := Build_IsBiInv _ _ _ succ_sect pred succ_is_retr succ_is_sect.

Definition biinv_int_succ : BiInv Int Int
  := Build_BiInv _ _ succ _.

(** The predecessor is an equivalence on [Int]. *)
#[export] Instance isequiv_int_pred : IsEquiv pred
  := isequiv_isbiinv_retr succ.

(** ** Induction and recursion principles for Int *)

Definition int_ind_equiv {P : Int -> Type} (t0 : P zero_i)
  (e : forall z : Int, P z -> P (succ z)) {iseq : forall z, IsEquiv (e z)}
  : forall z, P z.
Proof.
  snapply (int_ind t0 e).
  - intro z.
    exact ((e (pred z))^-1 o transport P (retr_is_sect_isbiinv biinv_int_succ z)^).
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

Section RecursionPrinciple.

  Context {P : Type} (t0 : P) (f : P -> P) (g1 g2 : P -> P)
    (s : g1 o f == idmap) (r : f o g2 == idmap).

  (** The recursion principle. *)
  Definition int_rec : Int -> P.
  Proof.
    snapply (int_ind t0 (fun _ => f) (fun _ => g1) (fun _ => g2)).
    all: intros z t; cbn.
    all: lhs napply transport_const.
    - apply s.
    - apply r.
  Defined.

  Definition int_rec_beta_succ_is_sect
    : forall z, ap int_rec (succ_is_sect z) = s (int_rec z).
  Proof.
    intro z.
    napply (cancelL (transport_const (succ_is_sect z) _)).
    lhs_V napply apD_const.
    napply int_ind_beta_succ_is_sect.
  Defined.

  Definition int_rec_beta_succ_is_retr
    : forall z, ap int_rec (succ_is_retr z) = r (int_rec z).
  Proof.
    intro z.
    napply (cancelL (transport_const (succ_is_retr z) _)).
    lhs_V napply apD_const.
    napply int_ind_beta_succ_is_retr.
  Defined.

End RecursionPrinciple.

(** The recursion principle phrased using a biinvertible map. *)
Definition int_rec_biinv {P : Type} (t0 : P) (f : P -> P) `{IsBiInv P P f}
  : Int -> P
  := int_rec t0 f (retr_biinv f) (sect_biinv f) (eissect_biinv f) (eisretr_biinv f).

(** The recursion principle phrased using a half-adjoint equivalence. *)
Definition int_rec_equiv {P : Type} (t0 : P) (f : P -> P) `{IsEquiv P P f}
  : Int -> P
  := @int_rec_biinv P t0 f (isbiinv_isequiv _ _).

(** Equivalence iteration. *)
Definition int_iter {A} (f : A -> A) `{!IsEquiv f} (z : Int) (a0 : A) : A
  := int_rec_equiv a0 f z.

Section Uniqueness.

  Context {P : Type} (e : BiInv P P).

  (** The following uniqueness principle states that if two maps out of [Int] agree on 0 and commute with the successor, then they are homotopic. *)
  Definition int_homotopic_two_fun_biinv (k1 : Int -> P) (k2 : Int -> P)
    (p0 : k1 zero_i = k2 zero_i) (pf1 : k1 o succ == e o k1) (pf2 : k2 o succ == e o k2)
    : k1 == k2.
  Proof.
    snapply int_ind_equiv; cbn beta.
    - exact p0.
    - intro z.
      exact (equiv_concat_l (pf1 z) _ oE equiv_concat_r (pf2 z)^ _ oE equiv_ap e _ _).
    - exact _.
  Defined.

  (** As a special case, we can characterize the recursor. *)
  Definition int_homotopic (t0 : P) (k : Int -> P)
    (p0 : k zero_i = t0) (pf : k o succ == e o k)
    (rec := int_rec_biinv t0 e)
    : k == rec
    := int_homotopic_two_fun_biinv k rec p0 pf (fun _ => idpath).

End Uniqueness.

(** The same uniqueness principle but for half-adjoint equivalences. *)
Definition int_homotopic_two_fun_equiv {P : Type} (f : P -> P)
  {e' : IsEquiv f} (k1 : Int -> P) (k2 : Int -> P)
  (p0 : k1 zero_i = k2 zero_i) (pf1 : k1 o succ == f o k1)
  (pf2 : k2 o succ == f o k2)
  : forall (z : Int), k1 z = k2 z
  := int_homotopic_two_fun_biinv (Build_BiInv P P _ (isbiinv_isequiv f e')) k1 k2 p0 pf1 pf2.

(** ** [Int] is equivalent to [SInt] *)

Section IntEquiv.

  Definition InttoIntIT : Int -> SInt
    := int_rec zero int_succ int_pred int_pred int_succ_pred int_pred_succ.

  Definition IntITtoInt : SInt -> Int.
  Proof.
    intro s; induction s as [|n IHz|n IHz].
    - exact zero_i.
    - exact (succ IHz).
    - exact (pred IHz).
  Defined.

  Definition IntITtoint_is_rinv : InttoIntIT o IntITtoInt == idmap.
  Proof.
    intro s; induction s as [|[|n] IHz|[|n] IHz].
    1, 2, 4: reflexivity.
    - exact (ap int_succ IHz).
    - exact (ap int_pred IHz).
  Defined.

  Definition IntITtoint_comp_succ : IntITtoInt o int_succ == succ o IntITtoInt.
  Proof.
    intro s; induction s as [|[|n] IHz|[|n] IHz].
    1-3: reflexivity.
    all: symmetry; exact (retr_is_sect_isbiinv succ _).
  Defined.

  Definition IntITtoint_is_linv : IntITtoInt o InttoIntIT == idmap.
  Proof.
    napply (int_homotopic_two_fun_biinv biinv_int_succ).
    1,3: reflexivity.
    intro z; simpl.
    apply IntITtoint_comp_succ.
  Defined.

  (** [IntITtoInt] is biinvertible.  It follows from typeclass inference that it is an equivalence. *)
  #[export] Instance isbiinv_IntITtoInt : IsBiInv IntITtoInt
    := Build_IsBiInv _ _ _ _ _ IntITtoint_is_linv IntITtoint_is_rinv.

  (** Since [SInt] is a set, therefore also [Int] is a set. *)
  #[export] Instance ishset_int
    : IsHSet Int
    := istrunc_isequiv_istrunc SInt _.

End IntEquiv.

(** From the equivalence to [SInt] we can deduce another induction principle for [int].  This one has weak hypotheses, but since [HN 1 (HP 0 t)] doesn't necessarily transport to [t] along [succ_is_sect 0], it is impossible for it to compute well on general [pred] and [succ] operations.  Passing through [SInt] normalizes terms giving us a canonical choice. *)
Definition int_ind_sint (P : Int -> Type)
  (H0 : P zero_i)
  (HP : forall z, P z -> P (succ z))
  (HN : forall z, P z -> P (pred z))
  : forall z, P z.
Proof.
  equiv_intro IntITtoInt s.
  induction s as [|n IHz|n IHz].
  - exact H0.
  - destruct n as [|n].
    all: apply HP, IHz.
  - destruct n as [|n].
    all: apply HN, IHz.
Defined.

Definition int_ind_iff (P : Int -> Type)
  (t0 : P zero_i) (f : forall z : Int, P z <-> P (succ z))
  : forall z, P z.
Proof.
  srapply (int_ind_sint P t0).
  - intro z.  exact (fst (f z)).
  - equiv_intro succ z.
    refine (_ o snd (f z)).
    exact (transport P (succ_is_sect z)^).
Defined.

(** ** Printing and parsing *)

(** For now we pass through [SInt] for printing and parsing. *)
Definition int_to_number_int : Int -> Numeral.int := int_to_number_int o InttoIntIT.

Definition int_of_number_int : Numeral.int -> Int := IntITtoInt o int_of_number_int.

Number Notation Int int_of_number_int int_to_number_int : int_scope.

(** The following function reduces an integer expression by cancelling succesive successor and predecessor terms. *)
Definition int_reduce := IntITtoInt o InttoIntIT.

(** We can convert a [nat] to an [Int] by mapping [0] to [zero] and [S n] to [succ n].  Various operations on [nat] are preserved by this function. *)
Definition int_of_nat (n : nat) : Int
  := nat_iter n succ zero_i.

Coercion int_of_nat : nat >-> Int.

(** ** Integer arithmetic using [Int] *)

Notation "z .+1" := (succ z) : int_scope.
Notation "z .-1" := (pred z) : int_scope.

(** *** Negation *)

Definition int_neg (z : Int) : Int
  := int_rec_equiv zero_i pred z.

Notation "- z" := (int_neg z) : int_scope.

(** Negation is involutive. *)
Definition int_neg_neg (z : Int) : - - z = z.
Proof.
  revert z.
  by srapply (int_homotopic_two_fun_equiv succ).
Defined.

(** Negation is an equivalence. *)
#[export] Instance isequiv_int_neg : IsEquiv int_neg.
Proof.
  snapply (isequiv_adjointify int_neg int_neg).
  1,2: napply int_neg_neg.
Defined.

(** Negation is injective. *)
Definition isinj_int_neg (x y : Int) : - x = - y -> x = y
  := equiv_inj int_neg.

(** The negation of a successor is the predecessor of the negation. *)
Definition int_neg_succ (z : Int) : - succ z = pred (-z)
  := idpath.

(** The negation of a predecessor is the successor of the negation. *)
Definition int_neg_pred (z : Int) : - pred z = succ (- z)
  := idpath.

(** *** Addition *)

(** We define addition by recursion on the first argument. *)
Definition int_add (x y : Int) : Int
  := int_iter succ x y.

Infix "+" := int_add : int_scope.
Infix "-" := (fun x y => x + -y) : int_scope.

(** Integer addition with zero on the left is the identity by definition. *)
Definition int_add_0_l (z : Int) : 0 + z = z
  := idpath.

(** Integer addition with zero on the right is the identity. *)
Definition int_add_0_r (z : Int) : z + 0 = z.
Proof.
  revert z.
  by srapply (int_homotopic_two_fun_equiv succ).
Defined.

(** Adding a successor on the left is the successor of the sum. *)
Definition int_add_succ_l (x y : Int) : (succ x) + y = succ (x + y)
  := idpath.

(** Adding a predecessor on the left is the predecessor of the sum. *)
Definition int_add_pred_l (x y : Int) : (pred x) + y = pred (x + y)
  := idpath.

(** Adding a successor on the right is the successor of the sum. *)
Definition int_add_succ_r (x y : Int) : x + (succ y) = succ (x + y).
Proof.
  revert x.
  by srapply (int_homotopic_two_fun_equiv succ).
Defined.

(** Adding a predecessor on the right is the predecessor of the sum. *)
Definition int_add_pred_r (x y : Int) : x + (pred y) = pred (x + y).
Proof.
  revert x.
  srapply (int_homotopic_two_fun_equiv succ); cbn beta.
  1,2: reflexivity.
  simpl; intro z.
  rewrite succ_is_sect.
  exact (retr_is_sect_isbiinv succ _)^.
Defined.

(** Integer addition with 1 on the left is the successor. *)
Definition int_add_1_l (z : Int) : 1 + z = succ z
  := idpath.

(** Integer addition with 1 on the right is the successor. *)
Definition int_add_1_r (z : Int) : z + 1 = succ z.
Proof.
  revert z.
  by srapply (int_homotopic_two_fun_equiv succ).
Defined.

(** Integer addition is commutative. *)
Definition int_add_comm (x y : Int) : x + y = y + x.
Proof.
  revert x.
  srapply (int_homotopic_two_fun_equiv succ); cbn beta.
  - by rewrite int_add_0_r.
  - reflexivity.
  - intro z.
    by rewrite int_add_succ_r.
Defined.

(** Integer addition is associative. *)
Definition int_add_assoc (x y z : Int) : x + (y + z) = x + y + z.
Proof.
  revert x.
  by srapply (int_homotopic_two_fun_equiv succ).
Defined.

(** Negation is a left inverse with respect to integer addition. *)
Definition int_add_neg_l (z : Int) : - z + z = 0.
Proof.
  revert z.
  srapply (int_homotopic_two_fun_equiv idmap); cbn beta.
  1,3: reflexivity.
  simpl; intro s.
  rewrite int_add_succ_r.
  apply succ_is_sect.
Defined.

(** Negation is a right inverse with respect to integer addition. *)
Definition int_add_neg_r (z : Int) : z - z = 0.
Proof.
  unfold "-"; by rewrite int_add_comm, int_add_neg_l.
Defined.

(** Negation distributes over addition. *)
Definition int_neg_add (x y : Int) : - (x + y) = - x - y.
Proof.
  revert x.
  by srapply (int_homotopic_two_fun_equiv pred).
Defined.

(** Addition is an equivalence with first argument fixed. *)
#[export] Instance isequiv_int_add_l (x : Int) : IsEquiv (int_add x).
Proof.
  srapply (isequiv_adjointify _ (int_add (-x))).
  all: simpl; intro y.
  all: lhs napply int_add_assoc.
  - by rewrite int_add_neg_r.
  - by rewrite int_add_neg_l.
Defined.

(** Addition is an equivalence with second argument fixed.  This also follows from the previous result and [int_add_comm], but this proof computes better. *)
#[export] Instance isequiv_int_add_r (y : Int) : IsEquiv (fun x => int_add x y).
Proof.
  snapply (isequiv_adjointify _ (fun x => int_add x (-y))).
  all: simpl; intro x.
  all: lhs_V napply int_add_assoc.
  - rewrite int_add_neg_l.
    apply int_add_0_r.
  - rewrite int_add_neg_r.
    apply int_add_0_r.
Defined.

(** *** Multiplication *)

(** We define multiplication by recursion on the first argument.  We can only define it at this stage as it depends on the proof that addition is an equivalence. *)
Definition int_mul (x y : Int) : Int
  := int_iter (fun z => int_add z y) x 0.

Infix "*" := int_mul : int_scope.

(** Multiplication with a successor on the left is the sum of the multplication without the successor and the multiplicand which was not a successor. *)
Definition int_mul_succ_l (x y : Int) : (succ x) * y = x * y + y
  := idpath.

(** Similarly, multiplication with a predecessor on the left is the sum of the multiplication without the predecessor and the negation of the multiplicand which was not a predecessor. *)
Definition int_mul_pred_l (x y : Int) : (pred x) * y = x * y - y
  := idpath.

(** Integer multiplication with zero on the left is zero by definition. *)
Definition int_mul_0_l (z : Int) : 0 * z = 0
  := idpath.

(** Integer multiplication with zero on the right is zero. *)
Definition int_mul_0_r (z : Int) : z * 0 = 0.
Proof.
  revert z.
  rapply (int_homotopic_two_fun_equiv idmap); cbn beta.
  1,3: reflexivity.
  simpl; intro z.
  by rewrite int_add_0_r.
Defined.

(** Integer multiplication with one on the left is the identity. *)
Definition int_mul_1_l (z : Int) : 1 * z = z
  := idpath.

(** Integer multiplication with one on the right is the identity. *)
Definition int_mul_1_r (z : Int) : z * 1 = z.
Proof.
  revert z.
  rapply (int_homotopic_two_fun_equiv (fun z => int_add z 1)); cbn beta.
  1,2: reflexivity.
  intro z.
  by rewrite int_add_1_r.
Defined.

(** Integer multiplication with -1 on the left is negation. *)
Definition int_mul_neg1_l (z : Int) : (-1) * z = - z
  := idpath.

(** Multiplying with a negation on the left is the same as negating the product. *)
Definition int_mul_neg_l (x y : Int) : - x * y = - (x * y).
Proof.
  revert x.
  rapply (int_homotopic_two_fun_equiv (fun x => int_add x (-y))); cbn beta.
  1,2: reflexivity.
  simpl; intro x.
  apply int_neg_add.
Defined.

(** Multiplying with a successor on the right is the sum of the multiplication without the successor and the product of the multiplicand which was not a successor and the multiplicand. *)
Definition int_mul_succ_r (x y : Int) : x * (succ y) = x + x * y.
Proof.
  revert x.
  rapply (int_homotopic_two_fun_equiv (fun x => int_add x (succ y))); cbn beta.
  1,2: reflexivity.
  simpl; intro z.
  rewrite int_add_succ_r.
  by rewrite int_add_assoc.
Defined.

(** Multiplying with a predecessor on the right is the sum of the multiplication without the predecessor and the product of the multiplicand which was not a predecessor and the negation of the multiplicand which was not a predecessor. *)
Definition int_mul_pred_r (x y : Int) : x * (pred y) = x * y - x.
Proof.
  revert x.
  rapply (int_homotopic_two_fun_equiv (fun x => int_add x (pred y))); cbn beta.
  1,2: reflexivity.
  intro z.
  rewrite int_mul_succ_l.
  rewrite <- int_add_assoc.
  simpl.
  rewrite (int_add_comm y _).
  rewrite int_add_pred_l.
  rewrite <- int_add_assoc.
  by rewrite (int_add_pred_r _ y).
Defined.

(** Integer multiplication is commutative. *)
Definition int_mul_comm (x y : Int) : x * y = y * x.
Proof.
  revert x.
  srapply (int_homotopic_two_fun_equiv (fun x => int_add x y)); cbn beta.
  - symmetry; apply int_mul_0_r.
  - reflexivity.
  - intro z.
    rewrite int_add_comm.
    apply int_mul_succ_r.
Defined.

(** Multiplying with a negation on the right is the same as negating the product. *)
Definition int_mul_neg_r (x y : Int) : x * - y = - (x * y).
Proof.
  rewrite !(int_mul_comm x).
  apply int_mul_neg_l.
Defined.

(** Multiplication distributes over addition on the left. *)
Definition int_dist_l (x y z : Int) : x * (y + z) = x * y + x * z.
Proof.
  revert x.
  srapply (int_homotopic_two_fun_equiv (fun x => int_add x (y + z))); cbn beta.
  1,2: reflexivity.
  simpl; intro x.
  rewrite <- (int_add_assoc (x*y) y).
  rewrite (int_add_comm y (x*z + z)).
  rewrite <- (int_add_assoc _ z y).
  rewrite (int_add_comm z y).
  by rewrite (int_add_assoc (x*y) _ _).
Defined.

(** Multiplication distributes over addition on the right. *)
Definition int_dist_r (x y z : Int) : (x + y) * z = x * z + y * z.
Proof.
  by rewrite int_mul_comm, int_dist_l, !(int_mul_comm z).
Defined.

(** Multiplication is associative. *)
Definition int_mul_assoc (x y z : Int) : x * (y * z) = x * y * z.
Proof.
  revert x.
  srapply (int_homotopic_two_fun_equiv (fun x => int_add x (y * z))); cbn beta.
  1,2: reflexivity.
  simpl; intro x.
  by rewrite int_dist_r.
Defined.

(** ** Results about iteration of equivalences *)

Definition int_iter_neg {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f (int_neg z) a = int_iter f^-1 z a.
Proof.
  revert z.
  by srapply (int_homotopic_two_fun_equiv f^-1).
Defined.

Definition int_iter_succ_l {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f (succ z) a = f (int_iter f z a)
  := idpath.

Definition int_iter_succ_r {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f (succ z) a = int_iter f z (f a).
Proof.
  revert z.
  by srapply (int_homotopic_two_fun_equiv f).
Defined.

Definition int_iter_pred_l {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f (pred z) a = f^-1 (int_iter f z a)
  := idpath.

Definition int_iter_pred_r {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f (pred z) a = int_iter f z (f^-1 a).
Proof.
  revert z.
  srapply (int_homotopic_two_fun_equiv f); cbn beta.
  1,3: reflexivity.
  intro z; simpl.
  exact (eissect f (int_iter f z a) @ (eisretr f (int_iter f z a))^).
Defined.

Definition int_iter_add {A} (f : A -> A) `{IsEquiv _ _ f} (x y : Int)
  : int_iter f (int_add x y) == int_iter f x o int_iter f y.
Proof.
  intro a; revert x.
  by srapply (int_homotopic_two_fun_equiv f _ _).
Defined.

(** If [g : A -> A'] commutes with automorphisms of [A] and [A'], then it commutes with iteration. *)
Definition int_iter_commute_map {A A'} (f : A -> A) `{!IsEquiv f}
  (f' : A' -> A') `{!IsEquiv f'}
  (g : A -> A') (p : g o f == f' o g) (z : Int) (a : A)
  : g (int_iter f z a) = int_iter f' z (g a).
Proof.
  revert z.
  srapply (int_homotopic_two_fun_equiv f' _ _); cbn beta.
  1,3: reflexivity.
  intro x; apply p.
Defined.

(** In particular, homotopic maps have homotopic iterations. *)
Definition int_iter_homotopic (z : Int) {A} (f f' : A -> A) `{!IsEquiv f} `{!IsEquiv f'}
  (h : f == f')
  : int_iter f z == int_iter f' z
  := int_iter_commute_map f f' idmap h z.

(** [int_iter f n x] doesn't depend on the proof that [f] is an equivalence. *)
Definition int_iter_agree (z : Int) {A} (f : A -> A) {ief ief' : IsEquiv f}
  : forall x, @int_iter A f ief z x = @int_iter A f ief' z x
  := int_iter_homotopic z f f (fun _ => idpath).

(** An important invariance property of iteration.  The most obvious proof attempts fail, for the reasons described in the comment for [int_ind_sint]. *)
Definition int_iter_invariant {A} (f : A -> A) `{!IsEquiv f}
  (P : A -> Type)
  (Psucc : forall a, P a -> P (f a))
  (Ppred : forall a, P a -> P (f^-1 a))
  (a0 : A) (Pa0 : P a0)
  : forall z, P (int_iter f z a0).
Proof.
  snapply int_ind_sint; cbn.
  - exact Pa0.
  - intros n IH. apply Psucc, IH.
  - intros n IH. apply Ppred, IH.
Defined.

(** ** Exponentiation of loops *)

Definition loopexp {A : Type} {a : A} (p : a = a) (z : Int) : (a = a)
  := int_iter (equiv_concat_r p a) z idpath.

Definition loopexp_succ_r {A : Type} {a : A} (p : a = a) (z : Int)
  : loopexp p (succ z) = loopexp p z @ p
  := int_iter_succ_l _ _ _.

Definition loopexp_pred_r {A : Type} {a : A} (p : a = a) (z : Int)
  : loopexp p (pred z) = loopexp p z @ p^
  := int_iter_pred_l _ _ _.

Definition loopexp_succ_l {A : Type} {a : A} (p : a = a) (z : Int)
  : loopexp p (succ z) = p @ loopexp p z.
Proof.
  lhs napply loopexp_succ_r.
  revert z.
  rapply (int_homotopic_two_fun_equiv (equiv_concat_r p a) _ _); cbn beta.
  - napply concat_1p_p1.
  - reflexivity.
  - intro z; simpl.
    by rewrite concat_p_pp.
Defined.

Definition loopexp_pred_l {A : Type} {a : A} (p : a = a) (z : Int)
  : loopexp p (pred z) = p^ @ loopexp p z.
Proof.
  rewrite loopexp_pred_r.
  revert z.
  rapply (int_homotopic_two_fun_equiv (equiv_concat_r p a) _ _); cbn beta.
  - napply concat_1p_p1.
  - intro z; simpl.
    rewrite 2 concat_pp_p.
    rewrite concat_Vp.
    by rewrite concat_pV.
  - intro z; simpl.
    by rewrite concat_p_pp.
Defined.

Definition ap_loopexp {A B} (f : A -> B) {a : A} (p : a = a) (z : Int)
  : ap f (loopexp p z) = loopexp (ap f p) z.
Proof.
  napply int_iter_commute_map.
  intro q; apply ap_pp.
Defined.

Definition loopexp_add {A : Type} {a : A} (p : a = a) x y
  : loopexp p (int_add x y) = loopexp p x @ loopexp p y. (*TODO: fix int_add*)
Proof.
  revert x.
  rapply (int_homotopic_two_fun_equiv (equiv_concat_r p a) _ _); cbn beta.
  - symmetry; apply concat_1p.
  - reflexivity.
  - intro z; simpl.
    rewrite 2 concat_pp_p.
    rewrite <- loopexp_succ_l.
    by rewrite <- loopexp_succ_r.
Defined.

(** Under univalence, exponentiation of loops corresponds to iteration of auto-equivalences. *)

Definition equiv_path_loopexp {A : Type} (p : A = A) (z : Int) (a : A)
  : equiv_path A A (loopexp p z) a = int_iter (equiv_path A A p) z a.
Proof.
  refine (int_iter_commute_map _ _ (fun p => equiv_path A A p a) _ _ _).
  intro q; cbn.
  napply transport_pp.
Defined.

Definition loopexp_path_universe `{Univalence} {A : Type} (f : A <~> A)
  (z : Int) (a : A)
  : transport idmap (loopexp (path_universe f) z) a = int_iter f z a.
Proof.
  revert f. equiv_intro (equiv_path A A) p.
  refine (_ @ equiv_path_loopexp p z a).
  refine (ap (fun q => equiv_path A A (loopexp q z) a) _).
  apply eissect.
Defined.

(** ** Converting between integers and naturals *)

(** [int_of_nat] preserves successors. *)
Definition int_nat_succ (n : nat)
  : (succ n)%int = (n.+1)%nat :> Int.
Proof.
  by induction n.
Defined.

(** [int_of_nat] preserves addition. Hence is a monoid homomorphism. *)
Definition int_nat_add (n m : nat)
  : (n + m)%int = (n + m)%nat :> Int.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - rewrite <- 2 int_nat_succ.
    rewrite int_add_succ_l.
    exact (ap _ IHn).
Defined.

(** [int_of_nat] preserves subtraction when not truncated. *)
Definition int_nat_sub (n m : nat)
  : (m <= n)%nat -> (n - m)%int = (n - m)%nat :> Int.
Proof.
  intros H.
  induction H as [|n H IHn].
  - lhs napply int_add_neg_r.
    by rewrite nat_sub_cancel.
  - rewrite nat_sub_succ_l; only 2: exact _.
    rewrite <- 2 int_nat_succ.
    rewrite int_add_succ_l.
    exact (ap _ IHn).
Defined.

(** [int_of_nat] preserves multiplication. This makes [int_of_nat] a semiring homomorphism. *)
Definition int_nat_mul (n m : nat)
  :  (n * m)%int = (n * m)%nat :> Int.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - rewrite <- int_nat_succ.
    rewrite int_mul_succ_l.
    rewrite nat_mul_succ_l.
    rhs_V napply int_nat_add.
    rewrite IHn.
    by rewrite int_add_comm.
Defined.
