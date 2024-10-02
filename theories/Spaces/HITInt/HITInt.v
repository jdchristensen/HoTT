Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Arrow Types.Sigma Cubical.DPath.


Module Export IntegersHIT.
 Section IntegersHIT.

  Universes i j u.
  Constraint i <= u, j <= u.

  Private Inductive IntegersHIT : Type@{u} :=
  | zero : IntegersHIT
  | succ : IntegersHIT -> IntegersHIT
  | pred1 : IntegersHIT -> IntegersHIT
  | pred2 : IntegersHIT -> IntegersHIT.

  Axiom sec : forall (z : IntegersHIT),
    (pred1 (succ z)) = z.

  Axiom ret : forall (z : IntegersHIT),
    (succ (pred2 z)) = z.

  (* Check IntegersHIT_ind. *)

  (* We define the induction principle. We need to use Fixpoint because its recursive*)
  Fixpoint IntegersHIT_ind'
    (P : IntegersHIT -> Type@{k})
    (t0 : P zero)
    (f : forall z : IntegersHIT, P z -> P (succ z))
    (g1 : forall z : IntegersHIT, P z -> P (pred1 z))
    (g2 : forall z : IntegersHIT, P z -> P (pred2 z))
    (s : forall (z : IntegersHIT) (t : P(z)), (@sec z # (g1 (succ z) (f z t)) = t))
    (r : forall (z : IntegersHIT) (t : P(z)), (ret z # (f (pred2 z) (g2 z t)) = t))
    (x : IntegersHIT)
    {struct x} : P x := 
    match x  with
    | zero => fun _ _ => t0
    | succ z => fun _ _ =>  f z (IntegersHIT_ind' P t0 f g1 g2 s r z)
    | pred1 z => fun _ _ =>  g1 z (IntegersHIT_ind' P t0 f g1 g2 s r z)
    | pred2 z => fun _ _ =>  g2 z (IntegersHIT_ind' P t0 f g1 g2 s r z)
    end s r.
    (*We need somehow make this depend on s and r as well*)


  Check IntegersHIT_ind'.
  About IntegersHIT_ind'.

  Axiom IntegersHIT_ind_beta_sec_sec
  : forall (P : IntegersHIT -> Type@{k})
    (t0 : P zero)
    (f : forall z : IntegersHIT, P z -> P (succ z))
    (g1 : forall z : IntegersHIT, P z -> P (pred1 z))
    (g2 : forall z : IntegersHIT, P z -> P (pred2 z))
    (s : forall (z : IntegersHIT) (t : P(z)), (sec z # (g1 (succ z) (f z t)) = t))
    (r : forall (z : IntegersHIT) (t : P(z)), (ret z # (f (pred2 z) (g2 z t)) = t))
    (z: IntegersHIT),
    (let f':= IntegersHIT_ind' P t0 f g1 g2 s r  in
    ((apD f' (sec z)) = s z (f' z))).

Print IntegersHIT_ind_beta_sec_sec.

  Axiom IntegersHIT_ind_beta_ret_sec
  : forall (P : IntegersHIT -> Type@{k})
    (t0 : P zero)
    (f : forall z : IntegersHIT, P z -> P (succ z))
    (g1 : forall z : IntegersHIT, P z -> P (pred1 z))
    (g2 : forall z : IntegersHIT, P z -> P (pred2 z))
    (s : forall (z : IntegersHIT) (t : P(z)), (sec z # (g1 (succ z) (f z t)) = t))
    (r : forall (z : IntegersHIT) (t : P(z)), (ret z # (f (pred2 z) (g2 z t)) = t))
    (z: IntegersHIT),
    (let f':= IntegersHIT_ind' P t0 f g1 g2 s r  in
    ((apD f' (ret z)) = r z (f' z))).

 End IntegersHIT.
End IntegersHIT.


