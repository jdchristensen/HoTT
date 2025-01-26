(** * Types of Sequences [nat -> X] *)

Require Import Basics Types.
Require Import Spaces.Nat.Core.

Open Scope nat_scope.
Open Scope type_scope.

(** ** Operations on sequences *)

(** The first term of a sequence. *)
Definition head {X : Type} (u : nat -> X) : X := u 0.

(** Shift of a sequence by 1 to the left. *)
Definition tail {X : Type} (u : nat -> X) : (nat -> X) := u o S.

(** Add a term to the start of a sequence. *)
Definition cons {X : Type} : X -> (nat -> X) -> (nat -> X).
Proof.
  intros x u [|n].
  - exact x.
  - exact (u n).
Defined.

Definition cons_head_tail {X : Type} (u : nat -> X)
  : cons (head u) (tail u) == u.
Proof.
  by intros [|n].
Defined.

Definition tail_cons {X : Type} (u : nat -> X) {x : X} : tail (cons x u) == u
  := fun _ => idpath.

(** ** Equivalence relations on sequences.  *)

(** For every [n : nat], we define a relation between two sequences that holds if and only if their first [n] terms are equal. *)
Definition seq_agree_on {X : Type} (n : nat) (s t : nat -> X) : Type
  := forall (m : nat), m < n -> s m = t m.

(** [seq_agree_on] has an equivalent inductive definition. *)
Definition seq_agree_on' {X : Type} (n : nat) : (nat -> X) -> (nat -> X) -> Type.
Proof.
  induction n.
  - intros u v; exact Unit.
  - intros u v; exact ((head u = head v) * (IHn (tail u) (tail v))).
Defined.

Definition seq_agree_terms {X : Type} {n : nat} {s t : nat -> X}
  : seq_agree_on n s t -> seq_agree_on' n s t.
Proof.
  intro h.
  induction n in s, t, h |- *.
  - exact tt.
  - simpl.
    exact (h 0 _, IHn _ _ (fun m hm => h m.+1 (_ hm))).
Defined.

Definition terms_seq_agree {X : Type} {n : nat} {s t : nat -> X}
  : seq_agree_on' n s t -> seq_agree_on n s t.
Proof.
  intros h m hm.
  induction m in n, s, t, h, hm |- *.
  - revert n hm h; nrapply gt_zero_ind; intros n h.
    exact (fst h).
  - induction n.
    + contradiction (not_lt_zero_r _ hm).
    + exact (IHm _ (tail s) (tail t) (snd h) _).
Defined.

Definition seq_lt_eq_iff_seq_agree {X : Type} {n : nat} {s t : nat -> X}
  : seq_agree_on n s t <-> seq_agree_on' n s t
  := (fun h => seq_agree_terms h, fun h => terms_seq_agree h).

(** Homotopic sequences agree on every number. *)
Definition seq_agree_homotopic {X : Type} {n : nat}
  {s t : nat -> X} (h : s == t)
  : seq_agree_on n s t
  := (fun m _ => h m).
