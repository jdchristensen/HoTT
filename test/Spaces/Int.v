From HoTT Require Import Basics.

Require Import Spaces.Int Spaces.SInt.

(** Test the conversion functions between int and sint. *)
Definition test1 : int_to_sint zero = sint_zero := idpath.

Definition test2 : int_to_sint (int_succ_sect zero) = sint_NegS 0 := idpath.

Definition test3 : int_to_sint (int_succ (int_succ_sect zero)) = sint_zero := idpath.

Definition test4 : sint_to_int sint_zero = zero := idpath.

Definition test5 : sint_to_int (sint_PosS 0) = int_succ zero := idpath.

Definition test6 : sint_to_int (sint_NegS 0) = int_pred zero := idpath.

(** Test the reduction functions for int. *)
Definition test7 : int_reduce (int_succ (int_pred (int_succ zero))) = int_succ zero := idpath.

Definition test8: int_reduce (int_succ_sect zero) = int_pred zero := idpath. 

Definition test9 : int_reduce (int_pred (int_succ (int_succ_sect zero))) = int_pred zero := idpath.


