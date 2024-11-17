Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.Universes.HSet
  HoTT.Spaces.Nat.Core
  HoTT.Spaces.Finite.FinNat
  HoTT.Spaces.Finite.Fin.

Local Open Scope nat_scope.

Definition fin_ind (P : forall n : nat, Fin n -> Type)
  (z : forall n : nat, P n.+1 fin_zero)
  (s : forall (n : nat) (k : Fin n), P n k -> P n.+1 (fsucc k))
  {n : nat} (k : Fin n)
  : P n k.
Proof.
  refine (transport (P n) (path_fin_to_finnat_to_fin k) _).
  refine (finnat_ind (fun n u => P n (finnat_to_fin u)) _ _ _).
  - intro. apply z.
  - intros n' u c.
    refine ((path_finnat_to_fin_succ _)^ # _).
    by apply s.
Defined.

Lemma fin_ind_beta_zero (P : forall n : nat, Fin n -> Type)
  (z : forall n : nat, P n.+1 fin_zero)
  (s : forall (n : nat) (k : Fin n), P n k -> P n.+1 (fsucc k)) (n : nat)
  : fin_ind P z s fin_zero = z n.
Proof.
  unfold fin_ind.
  generalize (path_fin_to_finnat_to_fin (@fin_zero n)).
  induction (path_fin_to_finnat_fin_zero n)^.
  intro p.
  destruct (hset_path2 1 p).
  lhs nrapply transport_1.
  nrapply finnat_ind_beta_zero.
Defined.

Lemma fin_ind_beta_fsucc (P : forall n : nat, Fin n -> Type)
  (z : forall n : nat, P n.+1 fin_zero)
  (s : forall (n : nat) (k : Fin n), P n k -> P n.+1 (fsucc k))
  {n : nat} (k : Fin n)
  : fin_ind P z s (fsucc k) = s n k (fin_ind P z s k).
Proof.
  unfold fin_ind.
  generalize (path_fin_to_finnat_to_fin (fsucc k)).
  induction (path_fin_to_finnat_fsucc k)^.
  intro p.
  refine (ap (transport (P n.+1) p) (finnat_ind_beta_succ _ _ _ _) @ _).
  generalize dependent p.
  induction (path_fin_to_finnat_to_fin k).
  induction (path_fin_to_finnat_to_fin k)^.
  intro p.
  induction (hset_path2 p (path_finnat_to_fin_succ (fin_to_finnat k))).
  apply transport_pV.
Defined.

Definition fin_rec (B : nat -> Type)
  : (forall n : nat, B n.+1) -> (forall (n : nat), Fin n -> B n -> B n.+1) ->
    forall {n : nat}, Fin n -> B n
  := fin_ind (fun n _ => B n).

Lemma fin_rec_beta_zero (B : nat -> Type)
  (z : forall n : nat, B n.+1)
  (s : forall (n : nat) (k : Fin n), B n -> B n.+1) (n : nat)
  : fin_rec B z s fin_zero = z n.
Proof.
  apply (fin_ind_beta_zero (fun n _ => B n)).
Defined.

Lemma fin_rec_beta_fsucc (B : nat -> Type)
  (z : forall n : nat, B n.+1)
  (s : forall (n : nat) (k : Fin n), B n -> B n.+1)
  {n : nat} (k : Fin n)
  : fin_rec B z s (fsucc k) = s n k (fin_rec B z s k).
Proof.
  apply (fin_ind_beta_fsucc (fun n _ => B n)).
Defined.

