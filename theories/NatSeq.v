(** ** Types of Sequences [nat -> X].  *)

Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import NatUStructure.
Require Import List.Core List.Theory.

Open Scope nat_scope.
Open Scope type_scope.

(** ** Operations on sequences. *)

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

(** ** Uniform structure on types of sequences. *)

(** Every type of the form [nat -> X] carries a uniform structure defined by setting [s =[n] t] if and only if their first [n] terms are equal. *)

Definition seq_agree_on {X : Type} (n : nat) : (nat -> X) -> (nat -> X) -> Type.
Proof.
  induction n.
  - intros u v; exact Unit.
  - intros u v; exact ((head u = head v) * (IHn (tail u) (tail v))).
Defined.

(** Two sequences are related in the above sense if and only if the corresponding terms up to the corresponding number [n] are equal. *)

Definition seq_agree_terms {X : Type} {n : nat} {s t : nat -> X}
  : (forall (m : nat), m < n -> s m = t m) -> seq_agree_on n s t.
Proof.
  intro h.
  induction n in s, t, h |- *.
  - exact tt.
  - simpl.
    exact (h 0 _, IHn _ _ (fun m hm => h m.+1 (_ hm))).
Defined.

Definition terms_seq_agree {X : Type} {n : nat} {s t : nat -> X}
  : seq_agree_on n s t -> (forall (m : nat), m < n -> s m = t m).
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
  : (forall (m : nat), m < n -> s m = t m) <-> seq_agree_on n s t
  := (fun h => seq_agree_terms h, fun h => terms_seq_agree h).

Definition seq_agree_homotopic {X : Type} {n : nat}
  {s t : nat -> X} (h : s == t)
  : seq_agree_on n s t
  := seq_agree_terms (fun m _ => h m).

Global Instance sequence_type_us {X : Type} : UStructure (nat -> X) | 10.
Proof.
  snrapply Build_UStructure.
  - exact seq_agree_on.
  - intros n u.
    by apply seq_agree_homotopic.
  - induction n.
    + exact (fun _ _ _ => tt).
    + exact (fun _ _ h => ((fst h)^, IHn _ _ (snd h))).
  - induction n.
    + exact (fun _ _ _ _ _ => tt).
    + exact (fun _ _ _ h1 h2 =>
               (fst h1 @ fst h2, IHn _ _ _ (snd h1) (snd h2))).
  - induction n.
    + exact (fun _ _ _ => tt).
    + exact (fun _ _ h => (fst h, IHn _ _ (snd h))).
Defined.

Definition cons_of_eq {X : Type} {n : nat} {s t : nat -> X} {x : X}
  (h : s =[n] t)
  : (cons x s) =[n.+1] (cons x t)
  := (idpath, h).

(** We can also rephrase the definition of [seq_agree_on] using the [list_restrict] function. *)
Definition list_restrict_eq_iff_seq_lt_eq {A : Type} {n : nat} {s t : nat -> A}
  : (list_restrict s n = list_restrict t n) <->
    (forall (m : nat), m < n -> s m = t m).
Proof.
  constructor.
  - intros h m hm.
    lhs_V srapply (nth'_list_restrict s hm ((length_list_restrict _ _)^ # hm)).
    rhs_V srapply (nth'_list_restrict t hm ((length_list_restrict _ _)^ # hm)).
    exact (nth'_path_list h _ _).
  - intro h.
    apply (path_list_nth' _ _
            ((length_list_restrict s n) @ (length_list_restrict t n)^)).
    intros i Hi.
    lhs srapply (nth'_list_restrict s ((length_list_restrict s n ) # Hi) Hi).
    rhs srapply (nth'_list_restrict t ((length_list_restrict s n) # Hi)
                  (length_list_restrict s n @ (length_list_restrict t n)^ # _)).
    exact (h i ((length_list_restrict s n) # Hi)).
Defined.

Definition list_restrict_eq_iff_seq_agree {A : Type} {n : nat} {s t : nat -> A}
  : list_restrict s n = list_restrict t n <-> s =[n] t
  := iff_compose list_restrict_eq_iff_seq_lt_eq seq_lt_eq_iff_seq_agree.

(** ** Continuity. *)

(** A uniformly continuous function takes homotopic sequences to outputs that are equivalent with respect to the structure on [Y]. *)
Definition uniformly_continuous_extensionality
  {X Y : Type} {usY : UStructure Y} (p : (nat -> X) -> Y) {m : nat}
  (c : uniformly_continuous p)
  {u v : nat -> X} (h : u == v)
  : p u =[m] p v
  := (c m).2 u v (seq_agree_homotopic h).

(** Composing a uniformly continuous function with the [cons] operation decreases the modulus by 1. Maybe this can be done with greater generality for the structure on [Y]. *)
Definition cons_decreases_modulus {X Y : Type}
  (p : (nat -> X) -> Y) (n : nat) (b : X)
  (hSn : is_modulus_of_uniform_continuity n.+1 p)
  : is_modulus_of_uniform_continuity n (p o cons b).
Proof.
  intros u v huv.
  apply hSn.
  exact (cons_of_eq huv).
Defined.
