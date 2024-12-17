Require Import Basics Types.
Require Import Spaces.Nat.Core.
Require Import Spaces.Finite.FinNat.
Require Import NatSeq.
Require Import ExcludedMiddle.
Require Import Spaces.List.Core Spaces.List.Paths Spaces.List.Theory.
Require Import Algebra.Rings.Vector.

Open Scope nat_scope.
Open Scope type_scope.
Open Scope list_scope.

(** Left to prove:
- LEM => BI
- Monotone BI => FAN *)

(** Converting a finite sequence into a list. This is taken from Build_Vector. *)
Definition Build_list {A : Type} (n : nat) (f : forall (i : nat), (i < n) -> A)
  : list A
  := list_map (fun '(i; Hi) => f i Hi) (seq' n).

Definition length_Build_list {A : Type} (n : nat)
  (f : forall (i : nat), (i < n) -> A)
  : length (Build_list n f) = n.
Proof.
  lhs nrapply length_list_map.
  apply length_seq'.
Defined.

(** Converse to path_vector: equal vectors have the same entries. *)
Definition vector_path {A : Type} {n : nat} {v1 v2 : Vector A n}
  (h : v1 = v2) (i : nat) (H : i < n)
  : entry v1 i = entry v2 i
  := match h with idpath => 1 end.

Definition empty_Vector (A : Type) : Vector A 0 := (nil; idpath).

Definition empty_if_length_0 {A : Type} (v : Vector A 0)
  : v = empty_Vector A
  := path_vector _ _ _ (fun i Hi => Empty_rec (not_lt_zero_r i Hi)).

(** Concatenation of vectors. *)
Definition Vector_app {A : Type} {m n : nat} (u : Vector A m) (v : Vector A n)
  : Vector A (m + n).
Proof.
  exists (u.1 ++ v.1).
  lhs nrapply length_app.
  exact (ap011 _ u.2 v.2).
Defined.

Definition term_to_Vector {A : Type} (a : A) : Vector A 1
  := Build_Vector A 1 (fun _ _ => a).

(** Add [a] to the end of the sequence. *)
Definition append {A : Type} {n : nat} (s : Vector A n) (a : A)
  : Vector A (n + 1)
  := Vector_app s (term_to_Vector a).

(** Restrict an infinite sequence to a finite sequence represented by a vector. *)
Definition restrict {A : Type} (s : nat -> A) (n : nat) : Vector A n
  := Build_Vector A n (fun m _ => s m).

Definition entry_restrict {A : Type} (s : nat -> A) (n : nat) i {Hi : (i < n)}
  : entry (restrict s n) i = s i
  := entry_Build_Vector _ _.

(** Restrict an infinite sequence to a finite sequence represented by a list. *)
Definition list_restrict {A : Type} (s : nat -> A) (n : nat) : list A
  := Build_list n (fun m _ => s m).

Definition list_restrict_length {A : Type} (s : nat -> A) (n : nat)
  : length (list_restrict s n) = n
  := length_Build_list _ _.

Definition list_restrict_length' {A : Type} (s t : nat -> A) (n : nat)
  : length (list_restrict s n) = length (list_restrict t n)
  := (list_restrict_length s n) @ (list_restrict_length t n)^.

(* This has been copied from vectors, can it be simplified? *)
Definition entry_list_restrict {A : Type} (s : nat -> A) (n : nat)
  {i : nat} (Hi : i < n)
  : nth' (list_restrict s n) i ((list_restrict_length s n)^ # Hi) = s i.
Proof.
  snrefine (nth'_list_map _ _ _ (_^ # Hi) _ @ _).
  - nrapply length_seq'.
  - exact (ap s (nth'_seq' _ _ _)).
Defined.

Definition entry_list_restrict' {A : Type} (s : nat -> A) (n : nat)
  {i : nat} (Hi : i < length (list_restrict s n))
  : nth' (list_restrict s n) i Hi = s i.
Proof.
  snrefine (nth'_list_map _ _ _ (_^ # Hi) _ @ _).
  - nrapply ((length_seq' n) @ (list_restrict_length s n)^).
  - exact (ap s (nth'_seq' _ _ _)).
Defined.

Definition restrict_eq_iff {A : Type} {n : nat} {u v : nat -> A}
  : (restrict u n = restrict v n) <-> (forall (m : nat), m < n -> u m = v m).
Proof.
  constructor.
  - intros h m hm.
    lhs_V srapply entry_restrict; rhs_V srapply entry_restrict.
    exact (ap (fun l => entry l m) h).
  - intro h.
    apply path_vector.
    intros i Hi.
    lhs nrapply entry_restrict; rhs nrapply entry_restrict.
    exact (h i Hi).
Defined.

(** Two equal lists have the same elements in the same positions. *)
Definition nth'_path_list {A : Type} {l1 l2 : list A}
  (p : l1 = l2) {n : nat} (Hn : n < length l1)
  : nth' l1 n Hn = nth' l2 n ((ap _ p) # Hn)
  := match p with idpath => idpath end.

Definition nth'_path_list' {A : Type} {l1 l2 : list A}
  (p : l1 = l2) {n : nat} (Hn1 : n < length l1) (Hn2 : n < length l2)
  : nth' l1 n Hn1 = nth' l2 n Hn2.
Proof.
  destruct p.
  by apply nth'_nth'.
Defined.

Definition restrict_tail_eq {A : Type} {n : nat} {u v : nat -> A}
  (h : restrict u n.+1 = restrict v n.+1)
  : restrict (NatSeq.tail u) n = restrict (NatSeq.tail v) n.
Proof.
  apply path_vector.
  intros i Hi.
  lhs nrapply entry_restrict; rhs nrapply entry_restrict.
  unfold NatSeq.tail.
  pose (h' := vector_path h i.+1 _).
  repeat rewrite entry_restrict in h'.
  exact h'.
Defined.

Definition seq_agree_res {A : Type} {n : nat} {u v : nat -> A}
  (h : restrict u n = restrict v n)
  : u =[n] v.
Proof.
  induction n in u, v, h |- *.
  - exact tt.
  - constructor.
    + unfold NatSeq.head.
      exact (fst restrict_eq_iff h 0 _).
    + exact (IHn _ _ (restrict_tail_eq h)).
Defined.

Definition res_seq_agree {A : Type} {n : nat} {u v : nat -> A}
  (h : u =[n] v)
  : restrict u n = restrict v n.
Proof.
  apply path_vector.
  intros i Hi.
  induction n in u, v, h, i, Hi |-*.
  - contradiction (not_lt_zero_r _ Hi).
  - lhs srapply entry_restrict; rhs srapply entry_restrict; induction i.
    + exact (fst h).
    + pose (ih := IHn (NatSeq.tail u) (NatSeq.tail v) (snd h) i _).
      repeat rewrite entry_restrict in ih.
      rapply ih.
Defined.

Definition seq_agree_iff_res {A : Type} {n : nat} {u v : nat -> A}
  : (u =[n] v) <-> restrict u n = restrict v n
  := (fun h => res_seq_agree h, fun h => seq_agree_res h).

Definition list_restrict_eq_iff {A : Type} {n : nat} {s t : nat -> A}
  : (list_restrict s n = list_restrict t n) <-> (forall (m : nat), m < n -> s m = t m).
Proof.
  constructor.
  - intros h m hm.
    lhs_V srapply entry_list_restrict.
    rhs_V srapply entry_list_restrict.
    exact (nth'_path_list' h _ _).
  - intro h.
    apply (path_list_nth' _ _ (list_restrict_length' s t n)).
    intros i Hi.
    lhs srapply entry_list_restrict'.
    rhs srapply (entry_list_restrict' t).
    exact (h i ((list_restrict_length s n) # Hi)).
Defined.

Definition seq_agree_iff_res' {A : Type} {n : nat} {s t : nat -> A}
  : list_restrict s n = list_restrict t n <-> (s =[n] t)
  := iff_compose list_restrict_eq_iff iff_us_sequence_eq.

(** * Bar Induction. *)

(** A family [B] on a type of lists is a bar if every infinite sequence restricts to a finite sequence in [B]. *)
Definition is_bar {A : Type} (B : list A -> Type)
  := forall (s : nat -> A), {n : nat & B (list_restrict s n)}.

(** A bar is uniform if there is an upper bound for the length of restrictions of infinite sequences in it. *)
Definition is_uniform_bar {A : Type} (B : list A -> Type)
  := {M : nat & forall (s : nat -> A),
                  {n : (FinNat M) & B (list_restrict s n.1)}}.

(** A family [B] on a type of finite sequences is inductive if, for every list, concatenations with any term being in [B] implies that the list is in [B]. *)
Definition is_inductive {A : Type} (B : list A -> Type)
  := forall (l : list A), (forall (a : A), B (l++[a])) -> B l.

(** A family [B] on a type of finite sequences is monotone if for every list in [B] concatenations with any other lists are still in [B]. Equivalently, we can just check for concatenations with terms. *)
Definition is_monotone {A : Type} (B : list A -> Type)
  := forall (l1 l2 : list A), B l1 -> B (l1++l2).

Definition is_monotone' {A : Type} (B : list A ->Type)
  := forall (l : list A) (a : A), B l -> B (l++[a]).

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

Definition monotone_bar_induction_montone_bar_induction' (A : Type)
  : monotone_bar_induction A -> monotone_bar_induction' A.
Proof.
  intro MBI.
  intros B C sub monC indB barC.
  pose (P := fun v => forall w, B (v++w)).
  nrapply (MBI P).
  - intros u v H w.
    by rewrite <- app_assoc.
  (* I'm sure this can be faster. *)
  - intros l1 H [|a l2].
    + apply indB.
      intro a.
      specialize (H a nil).
      by rewrite app_nil; rewrite app_nil in H.
    + specialize (H a l2).
      by rewrite <- app_assoc in H.
  - intro s.
    exists (barC s).1.
    intro w.
    apply sub, monC, barC.
Defined.

(** * Full bar induction for a type implies that it is compact.  *)

(** We will prove Pi-compactness by showing that [forall a, P a] is decidable for any decidable family [P].  We make use of the following family over [list A] which has that goal as the value at [nil]. *)
Definition BI_pi_family {A : Type} (P : A -> Type) (l : list A)
  : Type
  := match l with
      | nil => Decidable (forall a, P a)
      | a :: nil => P a
      | _ => Empty
     end.

Definition is_bar_BI_pi_family {A : Type} {P : A -> Type}
  (dec : forall n : A, Decidable (P n))
  : is_bar (BI_pi_family P).
Proof.
  intro s.
  destruct (dec (s 0)) as [p|p'].
  - exact (1; p).
  - exists 0.
    simpl.
    exact (inr (fun (u : forall a, P a) => p' (u (s 0)))).
Defined.

Definition is_inductive_BI_pi_family {A : Type} (P : A -> Type)
  : is_inductive (BI_pi_family P).
Proof.
  intros l h.
  destruct l.
  - left; exact h.
  (* If [l] is not nil, then [h a] is a term of type [Empty]. *)
  - destruct l; cbn in *; contradiction.
Defined.

Definition is_pi_compact_bar_induction {A : Type} (BI : bar_induction A)
  {P : A -> Type} (dec : forall n : A, Decidable (P n))
  : Decidable (forall a, P a)
  := BI (BI_pi_family P)
          (is_inductive_BI_pi_family P) (is_bar_BI_pi_family dec).

(** We will also show that [A] is Sigma compact, using this family. *)
Definition BI_sig_family {A : Type} (P : A -> Type) (l : list A)
  : Type
  := match l with
      | nil => Decidable {a : A & P a}
      | n :: l' => (~(P n)) * (length l' = 0)
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
    exact (p', idpath).
Defined.

Definition is_inductive_BI_sig_family {A : Type} (P : A -> Type)
  : is_inductive (BI_sig_family P).
Proof.
  intros l h.
  induction l.
  - right. exact (fun pa => (fst (h pa.1) pa.2)).
  - simpl in h.
    pose (q := snd (h a)).
    rewrite length_app, nat_add_comm in q; simpl in q.
    contradiction (neq_nat_zero_succ _ q^).
Defined.

(** This implies [is_pi_compact_bar_induction] because Σ-compactness implies Π-compactness. A proof of that is in [CompactTypes.v] but I have not deleted this since I do not know the best order of dependencies yet. *)
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
  rewrite list_restrict_length in h, t.
  assert (y : s =[conn.1] u).
  { symmetry; apply seq_agree_iff_res', h. }
  refine ((conn.2 _ y)^ @ conn.2 _ _).
  transitivity u.
  - exact y.
  - exact t.
Defined.

(** The fan theorem implies that every continuous function is uniformly continuous. Current proof uses the full fan theorem. Less powerful versions might be enough. *)

Definition uniform_continuity_fan_theorem {A : Type} (fan : fan_theorem A)
  (p : (nat -> A) -> Bool) (conn : IsContinuous p)
  : uniformly_continuous p.
Proof.
  pose (fanapp := fan (uc_theorem_family p) (is_bar_uc_theorem_family p conn)).
  exists fanapp.1.
  intros u v h.
  apply (fanapp.2 u).2.
  - exact (ap _ (list_restrict_length _ _)).
  - rewrite list_restrict_length.
    exact ((us_rel_leq (_ (fanapp.2 u).1.2) h)).
Defined.
