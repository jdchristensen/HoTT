Require Import Basics.Overture Basics.Nat Basics.Tactics Basics.Decidable.
Require Import Basics.Numerals.Decimal Basics.Numeral.
Require Import Spaces.Nat.Core.

Unset Elimination Schemes.
Set Universe Minimization ToSet.

(** * The signed integers *)

(** In this file, we give a simple inductive type that represents the integers.  It is straightforward to show that this type has decidable equality and is therefore a set, and it is also straightforward to print and parse integers using this type.  However, we only use it for these purposes, and treat the HIT integers as our main definition of the integers, since they have an induction principle with better computational behaviour. *)

(** ** Definition *)

(** We define the signed integers as two copies of [nat] stuck together around a [zero]. *)
Inductive SInt : Type0 :=
| sNegS : nat -> SInt
| szero : SInt
| sPosS : nat -> SInt.

(** We can convert a [nat] to an [SInt] by mapping [0] to [szero] and [S n] to [sPosS n]. *)
Definition sint_of_nat (n : nat) : SInt :=
  match n with
  | O => szero
  | S n => sPosS n
  end.

(** Symmetrically, we can send [n] to "-n" in this way: *)
Definition negsint_of_nat (n : nat) : SInt :=
  match n with
  | O => szero
  | S n => sNegS n
  end.

(** ** Number Notations *)

(** Here we define some printing and parsing functions that convert the integers between numeral representations so that we can use notations such as [123] for [sPosS 122] and [-123] for [sNegS 122]. *)

(** Printing *)
Definition int_to_number_int (n : SInt) : Numeral.int :=
  match n with
  | sPosS m => IntDec (Pos (to_uint (S m)))
  | szero => IntDec (Pos (to_uint 0))
  | sNegS m => IntDec (Neg (to_uint (S m)))
  end.

(** Parsing *)
Definition int_of_number_int (d : Numeral.int) : SInt :=
  match d with
  | IntDec (Pos u) => sint_of_nat (of_uint u)
  | IntDec (Neg u) => negsint_of_nat (of_uint u)
  | IntHex (Hexadecimal.Pos u) => sint_of_nat (of_hex_uint u)
  | IntHex (Hexadecimal.Neg u) => negsint_of_nat (of_hex_uint u)
  end.

(** ** Successor, predecessor and negation *)

Definition sint_succ (n : SInt) : SInt :=
  match n with
  | sPosS n => sPosS (S n)
  | szero => sPosS 0
  | sNegS n => negsint_of_nat n
  end.

Definition sint_pred (n : SInt) : SInt :=
  match n with
  | sPosS n => sint_of_nat n
  | szero => sNegS 0
  | sNegS n => sNegS (S n)
  end.

Definition sint_neg@{} (x : SInt) : SInt :=
  match x with
  | sPosS x => sNegS x
  | szero => szero
  | sNegS x => sPosS x
  end.

(** The successor of a predecessor is the identity. *)
Definition sint_pred_succ@{} (x : SInt) : sint_succ (sint_pred x) = x.
Proof.
  by destruct x as [ | | []].
Defined.

(** The predecessor of a successor is the identity. *)
Definition sint_succ_pred@{} (x : SInt) : sint_pred (sint_succ x) = x.
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
  1,2: exact _. (* Uses decideable equality of [nat]. *)
Defined.

(** By Hedberg's theorem, we have that the integers are a set. *)
Global Instance ishset_int@{} : IsHSet SInt := _.

(** ** Integer induction *)

(** The induction principle for signed integers is similar to the induction principle for natural numbers. However we have two induction hypotheses going in either direction starting from [0].  This is used only in HITInt.v. *)
Definition SInt_ind@{i} (P : SInt -> Type@{i})
  (H0 : P szero)
  (HP : forall n : nat, P (sint_of_nat n) -> P (sPosS n))
  (HN : forall n : nat, P (sint_neg (sint_of_nat n)) -> P (sNegS n))
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
