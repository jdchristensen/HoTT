Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.

Open Scope nat_scope.
Open Scope type_scope.

(** A uniform structure on a type consists of an equivalence relation for every natural number, each one being stronger than its predecessor. *)
Class UStructure (us_type : Type) := {
  us_rel : nat -> Relation us_type ;
  us_reflexive : forall n : nat, Reflexive (us_rel n) ;
  us_symmetric : forall n : nat, Symmetric (us_rel n) ;
  us_transitive : forall n : nat, Transitive (us_rel n) ;
  us_pred : forall (n : nat) (x y : us_type), us_rel n.+1 x y -> us_rel n x y
}.

Existing Instances us_reflexive us_symmetric us_transitive.

Notation "u =[ n ] v" := (us_rel n u v) (at level 70).

Definition us_rel_leq {X : Type} {struct : UStructure X}
  {m n : nat} (hm : m <= n) {u v : X} (h : u =[n] v)
  : u =[m] v.
Proof.
  induction hm.
  - assumption.
  - apply IHhm.
    by apply us_pred.
Defined.

(** Every type admits the trivial uniform structure with the standard identity type on every level. *)
Global Instance trivial_us {X : Type} : UStructure X.
Proof.
  srapply (Build_UStructure _ (fun n x y => (x = y))).
  exact (fun _ _ _ => idmap).
Defined.

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

(** A uniform structure on types of sequences, with the relation for [n : nat] given by: *)

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

Definition seq_agree_homotopic {X : Type} {n : nat}
  {s t : nat -> X} (h : s == t)
  : seq_agree_on n s t
  := seq_agree_terms (fun m _ => h m).

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

Global Instance us_sequence_type {X : Type} : UStructure (nat -> X).
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
    + exact (fun _ _ _ huv hvw =>
               ((fst huv) @ (fst hvw), IHn _ _ _ (snd huv) (snd hvw))).
  - induction n.
    + exact (fun _ _ _ => tt).
    + exact (fun _ _ h => (fst h, IHn _ _ (snd h))).
Defined.

Definition cons_of_eq {X : Type} {n : nat} {u v : nat -> X} {x : X}
  (h : u =[n] v)
  : (cons x u) =[n.+1] (cons x v)
  := (idpath, h).

Definition iff_us_sequence_eq {X : Type} {n : nat} {s t : nat -> X}
  : (forall (m : nat), m < n -> s m = t m) <-> s =[n] t
  := (fun h => seq_agree_terms h, fun h => terms_seq_agree h).

(** Definition of a continuous function depending on two uniform structures. *)
Definition IsContinuous
  {X Y : Type} {usX : UStructure X} {usY : UStructure Y} (p : X -> Y)
  := forall (u : X) (m : nat),
      {n : nat & forall v : X, (u =[n] v) -> p u =[m] p v}.

Definition uniformly_continuous {X Y : Type}
  {usX : UStructure X} {usY : UStructure Y} (p : X -> Y)
  := forall (m : nat),
      {n : nat & forall u v : X, (u =[n] v) -> p u =[m] p v}.

(** In the case that the target has the trivial uniform structure, it is useful (for now) to state uniform continuity by providing the specific modulus, which now only depends on the function. I might change the CompactTypes file instead.  *)
Definition is_modulus_of_uniform_continuity {X Y : Type} {usX : UStructure X}
  (n : nat) (p : X -> Y)
  := forall u v : X, (u =[n] v) -> p u = p v.

Definition uniformly_continuous_has_modulus {X Y :Type} {usX : UStructure X}
  {p : X -> Y} {n : nat} (c : is_modulus_of_uniform_continuity n p)
  : uniformly_continuous p
  := fun m => (n; c).

Definition iscontinuous_uniformly_continuous {X Y : Type}
  {usX : UStructure X} {usY : UStructure Y} (p : X -> Y)
  : uniformly_continuous p -> IsContinuous p
  := fun uc u m => ((uc m).1 ; fun v => (uc m).2 u v).

(** A uniformly continuous function takes homotopic sequences to outputs that are equivalent with respect to the structure on [Y]. *)
Definition uniformly_continuous_extensionality
  {X Y : Type} {usY : UStructure Y} (p : (nat -> X) -> Y) {m : nat}
  (c : uniformly_continuous p)
  {u v : nat -> X} (h : u == v)
  : p u =[m] p v
  := (c m).2 u v (seq_agree_homotopic h).

(** Composing a uniformly continuous function with the [cons] operation decreases the modulus by 1. I think this can be done with greater generality for the structure on Y. *)
Definition cons_decreases_modulus {X Y : Type}
  (p : (nat -> X) -> Y) (n : nat) (b : X)
  (hSn : is_modulus_of_uniform_continuity n.+1 p)
  : is_modulus_of_uniform_continuity n (p o cons b).
Proof.
  intros u v huv.
  apply hSn.
  exact (cons_of_eq huv).
Defined.
