(** * Bar induction and the fan theorem *)

Require Import Basics Types.
Require Import Spaces.Nat.Core.
Require Import Spaces.Finite.FinNat.
Require Import Misc.UStructures.
Require Import Spaces.NatSeq.Core Spaces.NatSeq.UStructure.
Require Import Spaces.List.Core Spaces.List.Paths Spaces.List.Theory.
Require Import Algebra.Rings.Vector.
Require Import BoundedSearch.

Local Open Scope nat_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.

(** A family [B] on a type of lists is a bar if every infinite sequence restricts to a finite sequence in [B]. *)
Definition is_bar {A : Type} (B : list A -> Type)
  := forall (s : nat -> A), {n : nat & B (list_restrict s n)}.

(** A bar is uniform if there is an upper bound for the length of restrictions of infinite sequences in it. *)
Definition is_uniform_bar {A : Type} (B : list A -> Type)
  := {M : nat & forall (s : nat -> A),
                  {n : (FinNat M) & B (list_restrict s n.1)}}.

(** A family [B] on a type of finite sequences is inductive if, for every list, concatenations with any term being in [B] implies that the list is in [B]. *)
Definition is_inductive {A : Type} (B : list A -> Type)
  := forall (l : list A), (forall (a : A), B (l ++ [a])) -> B l.

(** A family [B] on a type of finite sequences is monotone if for every list in [B] concatenation with any other list is still in [B]. Equivalently, we can just check the concatenations with lists of length one. *)
Definition is_monotone {A : Type} (B : list A -> Type)
  := forall (l1 l2 : list A), B l1 -> B (l1 ++ l2).

Definition is_monotone' {A : Type} (B : list A ->Type)
  := forall (l : list A) (a : A), B l -> B (l ++ [a]).

Definition is_monotone'_is_monotone {A : Type} (B : list A -> Type)
  (mon : is_monotone' B)
  : is_monotone B.
Proof.
  intros l1 l2; induction l2 as [|a l2 IHl2] in l1 |- *.
  - by rewrite app_nil.
  - intro h.
    rewrite (app_assoc l1 [a] l2).
    apply IHl2, mon, h.
Defined.

(** We state three forms of bar induction. Monotone bar induction implies decidable bar induction and full bar induction implies both others. *)

Definition decidable_bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (dec : forall (l : list A), Decidable (B l))
  (ind : is_inductive B)
  (bar : is_bar B),
  B nil.

Definition monotone_bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (mon : is_monotone B)
  (ind : is_inductive B)
  (bar : is_bar B),
  B nil.

Definition bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (ind : is_inductive B)
  (bar : is_bar B),
  B nil.

(** Monotone and full bar induction can be more generally stated for two families. The definitions are equivalent. *)

(** Are the definitions also equivalent in the decidable case? *)
Definition decidable_bar_induction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (dC : forall (l : list A), Decidable (C l))
  (ind : is_inductive B)
  (bar : is_bar C),
  B nil.

Definition monotone_bar_induction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (monC : is_monotone C)
  (indB : is_inductive B)
  (barC : is_bar C),
  B nil.

Definition bar_induction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (indB : is_inductive B)
  (barC : is_bar C),
  B nil.

Definition bar_induction'_bar_induction (A : Type) (BI : bar_induction A)
  : bar_induction' A
  := fun B C sub indB barC => BI B indB (fun s => ((barC s).1; sub _ (barC s).2)).

Definition monotone_bar_induction'_montone_bar_induction (A : Type)
  (MBI : monotone_bar_induction A)
  : monotone_bar_induction' A.
Proof.
  intros B C sub monC indB barC.
  pose (P := fun v => forall w, B (v ++ w)).
  nrapply (MBI P).
  - intros u v H w.
    by rewrite <- app_assoc.
  (* I'm sure this can be faster. *)
  - intros l1 H [|a l2].
    + apply indB.
      intro a.
      specialize (H a nil).
      by rewrite app_nil in *.
    + specialize (H a l2).
      by rewrite <- app_assoc in H.
  - intro s.
    exists (barC s).1.
    intro w.
    apply sub, monC, barC.
Defined.

Definition decidable_bar_induction'_monotone_bar_induction' (A : Type)
  (MBI : monotone_bar_induction' A)
  : decidable_bar_induction' A.
Proof.
  intros B C sub dC indB barC.
  pose (P := fun l => {n : nat & (n <= length l) * C (take n l)}).
  pose (Q := fun l => B l + P l).
  assert (dP : forall l : list A, Decidable (P l)).
  1: intro l; rapply decidable_search.
  assert (hqb : Q nil -> B nil).
  { intro q; destruct q as [b0|[n [hn hc]]].
    1: exact b0.
    exact (sub _ (take_nil _ # hc)). }
  apply hqb.
  apply (MBI Q P (fun l pl => inr pl)).
  - intros l1 l2 [n (cn1, cn2)].
    exists n; constructor.
    + rewrite length_app.
      apply (_ cn1).
    + exact (take_app l1 l2 cn1 # cn2).
  - intros l hl.
    destruct (dP l) as [t|f].
    1: exact (inr t).
    left. refine (indB _ _).
    intro a; destruct (hl a) as [b|[n [hn hc]]].
    1: exact b.
    destruct (equiv_leq_lt_or_eq hn) as [hn1|hn2].
    + contradiction f.
      assert (hln : n <= length l).
      { rewrite length_app, nat_add_comm in hn1.
        exact _. }
      exists n; constructor.
      * exact hln.
      * exact ((take_app l [a] hln)^ # hc).
    + refine (sub _ ((take_length_leq _ _ _) # hc)).
      apply equiv_leq_lt_or_eq; exact (inr hn2^).
  - intro s.
    exists (barC s).1; exists (barC s).1.
    constructor.
    + by rewrite (length_list_restrict s (barC s).1).
    + rewrite (take_length_leq _ _).
      1: exact (barC s).2.
      by rewrite (length_list_restrict s (barC s).1).
Defined.

Definition decidable_bar_induction_monotone_bar_induction (A : Type)
  (MBI : monotone_bar_induction A)
  : decidable_bar_induction A
  := fun B dec ind bar =>
      (decidable_bar_induction'_monotone_bar_induction' A
        (monotone_bar_induction'_montone_bar_induction A MBI))
      B B (fun _ => idmap) dec ind bar.

(** * Full bar induction for a type implies that it is compact.  *)

Definition BI_sig_family {A : Type} (P : A -> Type) (l : list A)
  : Type
  := match l with
      | nil => Decidable {a : A & P a}
      | n :: l' => ~(P n)
     end.

Definition is_bar_BI_sig_family {A : Type} {P : A -> Type}
  (dec : forall n : A, Decidable (P n))
  : is_bar (BI_sig_family P).
Proof.
  intro s.
  destruct (dec (s 0)) as [p|p'].
  - exists 0.
    simpl.
    exact (inl (s 0; p)).
  - exists 1.
    exact p'.
Defined.

Definition is_inductive_BI_sig_family {A : Type} (P : A -> Type)
  : is_inductive (BI_sig_family P).
Proof.
  intros l h.
  destruct l.
  - right. exact (fun pa => (h pa.1) pa.2).
  - exact (h a).
Defined.

Definition is_sig_compact_bar_induction {A : Type} (BI : bar_induction A)
  (P : A -> Type) (dec : forall n : A, Decidable (P n))
  : Decidable {a : A & P a}
  := BI (BI_sig_family P)
          (is_inductive_BI_sig_family P) (is_bar_BI_sig_family dec).

(** Full bar induction for [nat] implies the limited principle of omniscience, i.e., for every sequence of natural numbers we can decide whether every term is zero or there exists a non-zero term. *)

Definition LPO_bar_induction {BI : bar_induction nat} (s : nat -> nat)
  : (forall n : nat, s n = 0) + {n : nat & s n <> 0}.
Proof.
  destruct (is_sig_compact_bar_induction BI (fun n => s n <> 0) _) as [l|r].
  - right; exact l.
  - left; exact (fun n => stable (fun z : s n <> 0 => r (n; z))).
Defined.

(** * The Fan theorem.  *)

Definition decidable_fan_theorem (A : Type) :=
  forall (B : list A -> Type)
  (dec : forall l : list A, Decidable (B l))
  (bar : is_bar B),
  is_uniform_bar B.

Definition monotone_fan_theorem (A : Type) :=
  forall (B : list A -> Type)
  (mon : is_monotone B)
  (bar : is_bar B),
  is_uniform_bar B.

Definition fan_theorem (A : Type) :=
  forall (B : list A -> Type)
  (bar : is_bar B),
  is_uniform_bar B.

(** The family we use to apply the fan theorem in our proof that continuity implies uniform continuity *)
Definition uc_theorem_family {A : Type} (p : (nat -> A) -> Bool)
  : list A -> Type
  := fun l =>
      forall (u v : nat -> A) (h : list_restrict u (length l) = l),
        u =[length l] v -> p u = p v.

Definition is_bar_uc_theorem_family {A : Type}
  (p : (nat -> A) -> Bool) (conn : IsContinuous p)
  : is_bar (uc_theorem_family p).
Proof.
  intro s.
  specialize (conn s 0); unfold trivial_us, us_rel in conn.
  exists conn.1.
  unfold uc_theorem_family.
  intros u v h t.
  rewrite length_list_restrict in h, t.
  assert (y : s =[conn.1] u).
  { symmetry; apply list_restrict_eq_iff_seq_agree_lt, h. }
  refine ((conn.2 _ y)^ @ conn.2 _ _).
  transitivity u.
  - exact y.
  - exact t.
Defined.

(** The fan theorem implies that every continuous function is uniformly continuous. Current proof uses the full fan theorem. Less powerful versions might be enough. *)

Definition uniform_continuity_fan_theorem {A : Type} (fan : fan_theorem A)
  (p : (nat -> A) -> Bool) (con : IsContinuous p)
  : uniformly_continuous p.
Proof.
  pose (fanapp := fan (uc_theorem_family p) (is_bar_uc_theorem_family p con)).
  exists fanapp.1.
  intros u v h.
  apply (fanapp.2 u).2.
  - exact (ap _ (length_list_restrict _ _)).
  - rewrite length_list_restrict.
    exact ((us_rel_leq (_ (fanapp.2 u).1.2) h)).
Defined.
