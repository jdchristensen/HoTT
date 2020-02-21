(** Formalization of Hurewicz in HoTT *)

Require Import Basics Types Pointed.
Require Import Truncations.

Local Open Scope pointed_scope.
Local Open Scope nat_scope.

Global Instance isequiv_loops_functor {A B : pType} (f : A ->* B)
  : IsEquiv f -> IsEquiv (loops_functor f).
Proof.
  intro e.
  set (F := Build_pEquiv _ _ f e).
  change f with (pointed_equiv_fun _ _ F).
  clearbody F; clear f e.
  srapply isequiv_adjointify.
  1: apply loops_functor, (pequiv_inverse F).
  1,2: unfold Sect.
  1: change (loops_functor F o* (loops_functor F^-1*) == pmap_idmap).
  2: change (loops_functor F^-1* o* loops_functor F == pmap_idmap).
  1,2: apply pointed_htpy.
  1,2: refine ((loops_functor_compose _ _)^* @* _ @* loops_functor_idmap _).
  1,2: apply loops_2functor.
  1: apply peisretr.
  apply peissect.
Defined.

(** Theorem 2.1 *)
Theorem theorem_2_1 `{Funext} {n : nat} {X Y : pType}
  `{HX : IsConnected n X} `{HY : IsConnected n Y}
  `{TX : IsTrunc n.+1 X}  `{TY :IsTrunc n.+1 Y}
  : IsEquiv (@iterated_loops_functor X Y n).
Proof.
  revert X Y HX HY TX TY.
  induction n.
  1: exact _.
  intros X Y HX HY TX TY.
  simpl.
  
  srapply isequiv_commsq'.
Admitted.
(*
  { symmetry.
    intro f.
    serapply path_pmap.
    apply Pointed.pHomotopy
  1: serapply unfold_iterated_loops_functor.
  
  serapply IHn.
  serapply isequiv_adjointify.
  + simpl.
 *)
