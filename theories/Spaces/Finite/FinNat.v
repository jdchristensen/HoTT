Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HSet
  HoTT.Spaces.Nat
  HoTT.Spaces.Finite.Fin
  HoTT.DProp.

Definition FinNat (n : nat) : Type := {x : nat | x < n}.

Definition zero_finnat (n : nat) : FinNat n.+1
  := (0; tt).

Lemma path_zero_finnat (n : nat) (h : 0 < n.+1) : zero_finnat n = (0; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition succ_finnat {n : nat} (u : FinNat n) : FinNat n.+1
  := (u.1.+1; u.2).

Lemma path_succ_finnat {n : nat} (u : FinNat n) (h : u.1.+1 < n.+1)
  : succ_finnat u = (u.1.+1; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition last_finnat (n : nat) : FinNat n.+1
  := exist (fun x => x < n.+1) n (leq_refl n).

Lemma path_last_finnat (n : nat) (h : n < n.+1)
  : last_finnat n = (n; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition incl_finnat {n : nat} (u : FinNat n) : FinNat n.+1
  := (u.1; leq_trans u.1.+1 n n.+1 u.2 leqnSn).

Lemma path_incl_finnat (n : nat) (u : FinNat n) (h : u.1 < n.+1)
  : incl_finnat u = (u.1; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition finnat_ind (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : P n u.
Proof.
  induction n as [| n IHn].
  - elim u.2.
  - destruct u as [x h].
    destruct x as [| x].
    + exact (transport (P n.+1) (path_zero_finnat _ h) (z _)).
    + refine (transport (P n.+1) (path_succ_finnat (x; h) _) _).
      apply s. apply IHn.
Defined.

Lemma compute_finnat_ind_zero (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  (n : nat)
  : finnat_ind P z s (zero_finnat n) = z n.
Proof.
  reflexivity.
Defined.

Lemma compute_finnat_ind_succ (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n),
       P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : finnat_ind P z s (succ_finnat u) = s n u (finnat_ind P z s u).
Proof.
  exact (transport (fun p => transport _ p (s n u _)
                             = s n u (finnat_ind P z s u))
                   (hset_path2 1 (@path_succ_finnat n u u.2)) idpath).
Defined.

Monomorphic Definition is_bounded_fin_to_nat {n} (k : Fin n)
  : fin_to_nat k < n.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []].
    + apply (leq_trans _ n).
      * apply IHn.
      * apply leqnSn.
    + apply leq_refl.
Defined.

Monomorphic Definition fin_to_finnat {n} (k : Fin n) : FinNat n
  := (fin_to_nat k; is_bounded_fin_to_nat k).

Monomorphic Fixpoint finnat_to_fin {n : nat} : FinNat n -> Fin n
  := match n with
     | 0 => fun u => Empty_rec u.2
     | n.+1 => fun u =>
        match u with
        | (0; _) => fin_zero
        | (x.+1; h) => fsucc (finnat_to_fin (x; h))
        end
     end.

Lemma path_fin_to_finnat_fsucc {n : nat} (k : Fin n)
  : fin_to_finnat (fsucc k) = succ_finnat (fin_to_finnat k).
Proof.
  apply path_sigma_hprop.
  apply path_nat_fsucc.
Defined.

Lemma path_fin_to_finnat_fin_zero (n : nat)
  : fin_to_finnat (@fin_zero n) = zero_finnat n.
Proof.
  apply path_sigma_hprop.
  apply path_nat_fin_zero.
Defined.

Lemma path_fin_to_finnat_fin_incl {n : nat} (k : Fin n)
  : fin_to_finnat (fin_incl k) = incl_finnat (fin_to_finnat k).
Proof.
  reflexivity.
Defined.

Lemma path_fin_to_finnat_fin_last (n : nat)
  : fin_to_finnat (@fin_last n) = last_finnat n.
Proof.
  reflexivity.
Defined.

Lemma path_finnat_to_fin_succ {n : nat} (u : FinNat n)
  : finnat_to_fin (succ_finnat u) = fsucc (finnat_to_fin u).
Proof.
  reflexivity.
Defined.

Lemma path_finnat_to_fin_zero (n : nat)
  : finnat_to_fin (zero_finnat n) = fin_zero.
Proof.
  reflexivity.
Defined.

Lemma path_finnat_to_fin_incl {n : nat} (u : FinNat n)
  : finnat_to_fin (incl_finnat u) = fin_incl (finnat_to_fin u).
Proof.
  induction n as [| n IHn].
  - elim u.2.
  - destruct u as [x h].
    destruct x as [| x]; [reflexivity|].
    refine ((ap _ (ap _ (path_succ_finnat (x; h) h)))^ @ _).
    exact (ap fsucc (IHn (x; h))).
Defined.

Lemma path_finnat_to_fin_last (n : nat)
  : finnat_to_fin (last_finnat n) = fin_last.
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - exact (ap fsucc IHn).
Defined.

Lemma path_finnat_to_fin_to_finnat {n : nat} (u : FinNat n)
  : fin_to_finnat (finnat_to_fin u) = u.
Proof.
  induction n as [| n IHn].
  - elim u.2.
  - destruct u as [x h].
    destruct x as [| x].
    + destruct h. apply path_fin_to_finnat_fin_zero.
    + apply path_sigma_hprop.
      refine ((path_fin_to_finnat_fsucc _)..1 @ _).
      exact (ap S (IHn (x; h))..1).
Defined.

Lemma path_fin_to_finnat_to_fin {n : nat} (k : Fin n)
  : finnat_to_fin (fin_to_finnat k) = k.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []].
    + specialize (IHn k).
      refine (path_finnat_to_fin_incl (fin_to_finnat k) @ _).
      exact (ap fin_incl IHn).
    + apply path_finnat_to_fin_last.
Defined.

Definition equiv_fin_finnat (n : nat) : Fin n <~> FinNat n
  := equiv_adjointify fin_to_finnat finnat_to_fin
      path_finnat_to_fin_to_finnat
      path_fin_to_finnat_to_fin.
