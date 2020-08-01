(** Things that should maybe get merged into HomotopyGroup.v.
    Also lots of things in SmashHomotopy.v could be used to
    generalize the things in HomotopyGroup.v. *)

(* I'm sure these aren't all needed. *)
Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Algebra.AbGroups.
Require Import Truncations.
Require Import Spaces.Nat.
Require Import Modalities.ReflectiveSubuniverse.
Require Import WildCat.
Require Import Homotopy.HomotopyGroup.

Local Open Scope nat_scope.
Local Open Scope pointed_scope.

(** The type that the nth homotopy group will have. *)
Definition HomotopyGroup_type' (n : nat) : Type
  := match n with
      | 0 => pType
      | 1 => Group
      | _ => AbGroup
     end.

Definition HomotopyGroup_type_HomotopyGroup_type' (n : nat) : HomotopyGroup_type' n -> HomotopyGroup_type n
  := match n with
     | 0 => fun X => X
     | 1 => fun G => G
     (* This works because there is already a coercion AbGroup >-> Group. *)
     | _ => fun G => G
     end.

Coercion HomotopyGroup_type_HomotopyGroup_type' : HomotopyGroup_type' >-> HomotopyGroup_type.

Definition Pi' (n : nat) (X : pType) : HomotopyGroup_type' n.
Proof.
  destruct n.
  1: exact (Pi 0 X).
  destruct n.
  1: exact (Pi 1 X).
  simpl.
  srapply (Build_AbGroup (Pi n.+2 X) _ _ _ (isabgroup_pi 0 (iterated_loops n X))).
  (* [isabgroup_pi n X] also has the right type, but with the above choice, Coq can see quickly that [Pi n.+2 X] and [Pi 2 (iterated_loops n X)] are definitionally equal. *)
Defined.
