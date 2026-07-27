Require Import Basics.Overture Basics.Nat Basics.Tactics Basics.Decidable.
Require Import Basics.Numerals.Decimal Basics.Numeral.
Require Import Spaces.Nat.Core. (* TODO: Can we remove this?  Currently used for [nat_pred] below. *)

Unset Elimination Schemes.
Set Universe Minimization ToSet.

(** * The signed integers *)

(** In this file, we give a simple inductive type that represents the integers.  It is straightforward to show that this type has decidable equality and is therefore a set, and it is also straightforward to print and parse integers using this type.  However, we only use it for these purposes, and treat the HIT integers as our main definition of the integers, since they have an induction principle with better computational behaviour. *)

(** ** Definition *)

(** We define the signed integers as two copies of [nat] stuck together around a [zero]. *)
Inductive SInt : Type0 :=
| negS : nat -> SInt
| zero : SInt
| posS : nat -> SInt.

(** We can convert a [nat] to an [SInt] by mapping [0] to [zero] and [S n] to [posS n]. *)
Definition int_of_nat (n : nat) : SInt :=
  match n with
  | O => zero
  | S n => posS n
  end.

(** Symmetrically, we can send [n] to "-n" in this way: *)
Definition negint_of_nat (n : nat) : SInt :=
  match n with
  | O => zero
  | S n => negS n
  end.

(** ** Number Notations *)

(** Here we define some printing and parsing functions that convert the integers between numeral representations so that we can use notations such as [123] for [posS 122] and [-123] for [negS 122]. *)

(** Printing *)
Definition int_to_number_int (n : SInt) : Numeral.int :=
  match n with
  | posS m => IntDec (Pos (to_uint (S m)))
  | zero => IntDec (Pos (to_uint 0))
  | negS m => IntDec (Neg (to_uint (S m)))
  end.

(** Parsing *)
Definition int_of_number_int (d : Numeral.int) : SInt :=
  match d with
  | IntDec (Pos u) => int_of_nat (of_uint u)
  | IntDec (Neg u) => negint_of_nat (of_uint u)
  | IntHex (Hexadecimal.Pos u) => int_of_nat (of_hex_uint u)
  | IntHex (Hexadecimal.Neg u) => negint_of_nat (of_hex_uint u)
  end.

(** ** Successor, predecessor and negation *)

Definition int_succ (n : SInt) : SInt :=
  match n with
  | posS n => posS (S n)
  | zero => posS 0
  | negS n => negint_of_nat n
  end.

Definition int_pred (n : SInt) : SInt :=
  match n with
  | posS n => int_of_nat n
  | zero => negS 0
  | negS n => negS (S n)
  end.

Definition int_neg@{} (x : SInt) : SInt :=
  match x with
  | posS x => negS x
  | zero => zero
  | negS x => posS x
  end.

(** The successor of a predecessor is the identity. *)
Definition int_pred_succ@{} (x : SInt) : int_succ (int_pred x) = x.
Proof.
  by destruct x as [ | | []].
Defined.

(** The predecessor of a successor is the identity. *)
Definition int_succ_pred@{} (x : SInt) : int_pred (int_succ x) = x.
Proof.
  by destruct x as [[] | | ].
Defined.

(** ** Decidable Equality *)

(** The integers have decidable equality. *)
Global Instance decidable_paths_int@{} : DecidablePaths SInt.
Proof.
  intros [x | | x] [y | | y].
  2-4,6-8: right; intros; discriminate.
  2: by left.
  1,2: napply decidable_iff.
  1,3: split.
  1,3: napply ap.
  1,2: intros H; by injection H.
  1,2: exact _.
Defined.

(** By Hedberg's theorem, we have that the integers are a set. *)
Global Instance ishset_int@{} : IsHSet SInt := _.

(** ** Integer induction *)

(** The induction principle for signed integers is similar to the induction principle for natural numbers. However we have two induction hypotheses going in either direction starting from [0]. *)
(** TODO: This is slightly altered compared to Int.v, and I don't know which one is better. *)
(** TODO: This is used only in HITInt.v.  It may be possible to completely avoid it, which would then let us drop [int_of_nat] as well. *)
Definition SInt_ind@{i} (P : SInt -> Type@{i})
  (H0 : P zero)
  (HP : forall n : nat, P (int_of_nat n) -> P (posS n))
  (HN : forall n : nat, P (int_neg (int_of_nat n)) -> P (negS n))
  : forall x, P x.
Proof.
  intros [x | | x].
  - induction x as [|x IHx].
    + apply (HN 0%nat), H0.
    + apply (HN x.+1%nat), IHx.
  - exact H0.
  - induction x as [|x IHx].
    * apply (HP 0%nat), H0.
    * apply (HP x.+1%nat), IHx.
Defined.

(** We record these so that they can be used with the [induction] tactic. *)
Definition SInt_rect := SInt_ind.
Definition SInt_rec := SInt_ind.
