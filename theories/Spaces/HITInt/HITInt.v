Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Arrow Types.Sigma Cubical.DPath.
Require Import Spaces.Int.
Require Import Spaces.Nat.Core.


Module Export IntegersHIT.
 Section IntegersHIT.

  Universes i j u.
  Constraint i <= u, j <= u.

  Private Inductive IntegersHIT : Type@{u} :=
  | zero_i : IntegersHIT
  | succ : IntegersHIT -> IntegersHIT
  | pred1 : IntegersHIT -> IntegersHIT
  | pred2 : IntegersHIT -> IntegersHIT.

  Axiom sec : forall (z : IntegersHIT),
    (pred1 (succ z)) = z.

  Axiom ret : forall (z : IntegersHIT),
    (succ (pred2 z)) = z.

  (* Check IntegersHIT_ind. *)

  (* We define the induction principle. We need to use Fixpoint because its recursive*)
  Fixpoint IntegersHIT_ind
    (P : IntegersHIT -> Type@{k})
    (t0 : P zero_i)
    (f : forall z : IntegersHIT, P z -> P (succ z))
    (g1 : forall z : IntegersHIT, P z -> P (pred1 z))
    (g2 : forall z : IntegersHIT, P z -> P (pred2 z))
    (s : forall (z : IntegersHIT) (t : P(z)), (sec z # (g1 (succ z) (f z t)) = t))
    (r : forall (z : IntegersHIT) (t : P(z)), (ret z # (f (pred2 z) (g2 z t)) = t))
    (x : IntegersHIT)
    {struct x} : P x  
    := match x  with
    | zero_i => fun _ _ => t0
    | succ z => fun _ _ =>  f z (IntegersHIT_ind P t0 f g1 g2 s r z)
    | pred1 z => fun _ _ =>  g1 z (IntegersHIT_ind P t0 f g1 g2 s r z)
    | pred2 z => fun _ _ =>  g2 z (IntegersHIT_ind P t0 f g1 g2 s r z)
    end s r.
    (*This has to be dependent on s and r as well*)


  Check IntegersHIT_ind.
  About IntegersHIT_ind.

  Axiom IntegersHIT_ind_beta_sec_sec
  : forall (P : IntegersHIT -> Type@{k})
    (t0 : P zero_i)
    (f : forall z : IntegersHIT, P z -> P (succ z))
    (g1 : forall z : IntegersHIT, P z -> P (pred1 z))
    (g2 : forall z : IntegersHIT, P z -> P (pred2 z))
    (s : forall (z : IntegersHIT) (t : P(z)), (sec z # (g1 (succ z) (f z t)) = t))
    (r : forall (z : IntegersHIT) (t : P(z)), (ret z # (f (pred2 z) (g2 z t)) = t))
    (z: IntegersHIT),
    (let f':= IntegersHIT_ind P t0 f g1 g2 s r  in
    ((apD f' (sec z)) = s z (f' z))).

Print IntegersHIT_ind_beta_sec_sec.

  Axiom IntegersHIT_ind_beta_ret_sec
  : forall (P : IntegersHIT -> Type@{k})
    (t0 : P zero_i)
    (f : forall z : IntegersHIT, P z -> P (succ z))
    (g1 : forall z : IntegersHIT, P z -> P (pred1 z))
    (g2 : forall z : IntegersHIT, P z -> P (pred2 z))
    (s : forall (z : IntegersHIT) (t : P(z)), (sec z # (g1 (succ z) (f z t)) = t))
    (r : forall (z : IntegersHIT) (t : P(z)), (ret z # (f (pred2 z) (g2 z t)) = t))
    (z: IntegersHIT),
    (let f':= IntegersHIT_ind P t0 f g1 g2 s r  in
    ((apD f' (ret z)) = r z (f' z))).

 End IntegersHIT.
End IntegersHIT.

Check transport_const.
Check IntegersHIT_ind.

Definition IntegersHIT_rec
  (P: Type@{k})
  (t0 : P)
  (f :  P -> P)
  (g1 :  P -> P)
  (g2 :  P -> P)
  (s : forall  (t : P ), (g1 (f t)= t))
  (r : forall  (t : P ), (f (g2 t)= t))
  : IntegersHIT -> P.
Proof.
  srapply IntegersHIT_ind.
  1: exact t0.
  1: exact (fun _ => f).
  1: exact (fun _ => g1).
  1: exact (fun _ => g2).
  1: exact (fun z t => (transport_const (sec z) (g1 (f t))) @ (s t)). 
  1: exact (fun z t => (transport_const (ret z) (f (g2 t))) @ (r t)).
Defined.


Definition IntHITtoIntIT : IntegersHIT -> Int.
Proof.
  srapply IntegersHIT_rec.
  1: exact zero.
  1: exact int_succ.
  1: exact int_pred.
  1: exact int_pred.
  1: exact int_succ_pred.
  1: exact int_pred_succ.
Defined.

Definition IntITtoIntHIT
  (z : Int)
  : IntegersHIT.
Proof.
  induction z.
  -
    exact zero_i.
  - 
    exact (succ IHz).
  -
    exact (pred1 IHz).
Defined.

Compute IntITtoIntHIT (posS 5).

Compute IntITtoIntHIT (negS 1).

Compute IntITtoIntHIT zero.

Compute IntHITtoIntIT zero_i.

Compute IntHITtoIntIT (succ (pred2 zero_i)).

Compute IntHITtoIntIT (pred1 (succ (pred2 zero_i))).

Compute IntHITtoIntIT (succ (succ (succ zero_i))).

Definition int_succ_is_same 
(x y : Int) 
(t: (x = y))
: (int_succ x) = (int_succ y).
Proof.
  simpl.
  induction t.
  - reflexivity.
Defined. 

Definition int_pred_is_same 
(x y : Int) 
(t: (x = y))
: (int_pred x) = (int_pred y).
Proof.
  simpl.
  induction t.
  - reflexivity.
Defined. 

Definition linv
 (z : Int )
 : ((IntHITtoIntIT o IntITtoIntHIT) z) = z.
Proof.
  induction z as [|[|z] IHz|[|z] IHz].
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
  - 
    simpl.
    apply int_succ_is_same in IHz.
    apply IHz. 
  -
    simpl.
    reflexivity.
  -
    simpl.
    apply int_pred_is_same in IHz.
    apply IHz.
Defined.





