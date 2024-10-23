Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Arrow Types.Sigma Cubical.DPath.
Require Import Spaces.Int.
Require Import Spaces.Nat.Core.
Require Import Equiv.BiInv.

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
    (*This is dependent on s and r as well*)


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
  srapply (IntegersHIT_ind _ t0).
  1: exact (fun _ => f).
  1: exact (fun _ => g1).
  1: exact (fun _ => g2).
  1: exact (fun z t => (transport_const (sec z) (g1 (f t))) @ (s t)). 
  1: exact (fun z t => (transport_const (ret z) (f (g2 t))) @ (r t)).
Defined.

Definition pred1_is_pred2
  (z : IntegersHIT)
  : pred1 z = pred2 z
  := (ap pred1 ((ret z) ^)) @ sec(pred2 z).

Definition uniquenessZset
(P: Type@{k})
(* (l : IsHSet P) *)
(t0 : P)
(f :  P -> P)
(g1 :  P -> P)
(g2 :  P -> P)
(s : forall  (t : P ), (g1 (f t)= t))
(r : forall  (t : P ), (f (g2 t)= t))
(k: IntegersHIT -> P)
(p0 : (k zero_i) = t0)
(pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
(pg1 : forall (z : IntegersHIT), (g1 o k) z = (k o pred1) z)
(pg2 : forall (z : IntegersHIT), (g2 o k) z = (k o pred2) z)
(l: forall (z : IntegersHIT) (t : P ) (r : P ) (p: t = r) (q: t = r), (p = q))

: forall (z : IntegersHIT), k z = (IntegersHIT_rec P t0 f g1 g2 s r) z.
Proof.
snrapply IntegersHIT_ind.
-
  simpl.
  exact p0.
-
  simpl.
  intros.
  apply (ap f) in X.
  exact (((pf z)^) @ X).
-
  simpl.
  intros.
  apply (ap g1) in X.
  exact (((pg1 z)^) @ X).
- 
  simpl.
  intros.
  apply (ap g2) in X.
  exact (((pg2 z)^) @ X).
-
  simpl.
  intros.
  exact (l z (k z)  (IntegersHIT_rec P t0 f g1 g2 s r z) (transport (fun x : IntegersHIT => k x = IntegersHIT_rec P t0 f g1 g2 s r x)
(sec z) ((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t))) t).
-
  simpl. 
  intros.
  exact (l z (k z) (IntegersHIT_rec P t0 f g1 g2 s r z) (transport (fun x : IntegersHIT => k x = IntegersHIT_rec P t0 f g1 g2 s r x)
(ret z) ((pf (pred2 z))^ @ ap f ((pg2 z)^ @ ap g2 t))) t).
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

(* Compute IntHITtoIntIT (succ (succ zero_i)). *)


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

(* Compute IntITtoIntHIT (negS 5). *)


Definition IntITtoIntHIT_is_rinv
 (z : Int )
 : ((IntHITtoIntIT o IntITtoIntHIT) z) = z.
Proof.
  induction z as [|[|n] IHz|[|n] IHz].  
  -
    simpl.
    reflexivity.
  -
    simpl.
    reflexivity.
  - 
    apply (ap int_succ) in IHz.
    apply IHz. 
  -
    simpl.
    reflexivity.
  -
    simpl.
    apply (ap int_pred) in IHz.
    apply IHz.
Defined.

(* first mapping to set*)

Definition uniquenessZset
  (P: Type0)
  (t0 : P)
  (f :  P -> P)
  (g1 :  P -> P)
  (g2 :  P -> P)
  (s : forall  (t : P ), (g1 (f t)= t))
  (r : forall  (t : P ), (f (g2 t)= t))
  (k: IntegersHIT -> P)
  (p0 : (k zero_i) = t0)
  (pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
  (pg1 : forall (z : IntegersHIT), (g1 o k) z = (k o pred1) z)
  (pg2 : forall (z : IntegersHIT), (g2 o k) z = (k o pred2) z)
  (l: forall (z : IntegersHIT) (t : P ) (r : P ) (p: t = r) (q: t = r), (p = q))
  : forall (z : IntegersHIT), k z = (IntegersHIT_rec P t0 f g1 g2 s r) z.
Proof.
  snrapply IntegersHIT_ind.
  -
    simpl.
    exact p0.
  -
    simpl.
    intros.
    apply (ap f) in X.
    exact (((pf z)^) @ X).
  -
    simpl.
    intros.
    apply (ap g1) in X.
    exact (((pg1 z)^) @ X).
  - 
    simpl.
    intros.
    apply (ap g2) in X.
    exact (((pg2 z)^) @ X).
  -
    simpl.
    intros.
    exact (l z (k z)  (IntegersHIT_rec P t0 f g1 g2 s r z) (transport (fun x : IntegersHIT => k x = IntegersHIT_rec P t0 f g1 g2 s r x)
(sec z) ((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t))) t).
  -
    simpl. 
    intros.
    exact (l z (k z) (IntegersHIT_rec P t0 f g1 g2 s r z) (transport (fun x : IntegersHIT => k x = IntegersHIT_rec P t0 f g1 g2 s r x)
(ret z) ((pf (pred2 z))^ @ ap f ((pg2 z)^ @ ap g2 t))) t).
Defined.


(* 
    exact (l z _ _ (transport_const (sec z) ((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t))) t).
    exact (fun z t => l z _ _ (transport_const (sec z) ((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t))) t).
    exact (fun z t => (transport_const (sec z) (l z _ _ (ap (sec z) t) (((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t)))))).

    exact (l z (k z) (IntegersHIT_rec P t0 f g1 g2 s r z) (t) (transport_const (sec z)  ((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t)))).

 *)


Definition uniquenessZ
  (P: Type@{k})
  (t0 : P)
  (f :  P -> P)
  (g1 :  P -> P)
  (g2 :  P -> P)
  (s : forall  (t : P ), (g1 (f t)= t))
  (r : forall  (t : P ), (f (g2 t)= t))
  (k: IntegersHIT -> P)
  (p0 : (k zero_i) = t0)
  (pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
  (pg1 : forall (z : IntegersHIT), (g1 o k) z = (k o pred1) z)
  (pg2 : forall (z : IntegersHIT), (g2 o k) z = (k o pred2) z)
  : forall (z : IntegersHIT), k z = (IntegersHIT_rec P t0 f g1 g2 s r) z.
Proof.
  snrapply IntegersHIT_ind.
  -
    simpl.
    exact p0.
  -
    simpl.
    intros.
    apply (ap f) in X.
    exact (((pf z)^) @ X).
  -
    simpl.
    intros.
    apply (ap g1) in X.
    exact (((pg1 z)^) @ X).
  - 
    simpl.
    intros.
    apply (ap g2) in X.
    exact (((pg2 z)^) @ X).
  -
    simpl.
    intros.
     

  


Record pr_Bi (A B A' B' : Type) 
(a: A -> A') (b: B -> B') (e: A -> B) (BIe : (BiInv e)) (e': A' -> B') (BIe' : (BiInv e'))  := {
  p_e : forall (x: A), e'(a x) = b(e x);  
  p_g : forall (y: B), (proj1 (fst BIe')) (b y)= a ((proj1 (fst BIe)) y);
  p_h : forall (y: B), (proj1 (snd BIe')) (b y) = a ((proj1 (snd BIe)) y)
  (* p_s : forall (x: A),  ((proj2 ((fst BIe'))) (a x) = (ap (proj1 (fst BIe')) (p_e x)) @  (p_g (e x)) @ (ap a ((proj1 (fst BIe) x))))  *)
}. 



Compute IntITtoIntHIT (posS 5).

Compute IntITtoIntHIT (negS 1).

Compute IntITtoIntHIT zero. 

Compute IntHITtoIntIT zero_i.

Compute IntHITtoIntIT (succ (pred2 zero_i)).

Compute IntHITtoIntIT (pred1 (succ (pred2 zero_i))).

Compute IntHITtoIntIT (succ (succ (succ zero_i))).


Definition int_HIT_add 
  (x y : IntegersHIT) 
  : IntegersHIT.
Proof.
  revert x.
  snrapply IntegersHIT_rec.
  -
    exact y.
  - 
    exact succ.
  -
    exact pred1.
  - 
    exact pred2.
  -
    exact sec.
  -
    exact ret.
  
Defined.

Compute int_HIT_add (succ zero_i) (succ (succ (succ (pred1 zero_i)))).

Compute IntHITtoIntIT (int_HIT_add (succ zero_i) (succ (succ (succ (pred1 zero_i))))).

Context (y : IntegersHIT).

Compute int_HIT_add zero_i y.

Compute int_HIT_add (succ zero_i) y.



(* 
Definition int_HIT_add_commutative
  {x y: IntegersHIT}
  : (int_HIT_add x y) = (int_HIT_add y x).
Proof.
  revert x.
  snrapply IntegersHIT_ind; cbn beta.
  -
      *)

(* 
  snrapply (IntegersHIT_ind  *)





Compute (IntITtoIntHIT o IntHITtoIntIT) zero_i.

Compute (IntITtoIntHIT o IntHITtoIntIT) (succ zero_i).

Compute (IntITtoIntHIT o IntHITtoIntIT) (pred2 zero_i).

Compute (IntITtoIntHIT o IntHITtoIntIT) (pred1 zero_i).

Compute (IntITtoIntHIT o IntHITtoIntIT) (succ (pred2 (pred1 (succ zero_i)))).


Compute (succ ((IntITtoIntHIT o IntHITtoIntIT) (y))).

Compute (succ ((IntITtoIntHIT o IntHITtoIntIT) (succ y))).


Compute (((IntITtoIntHIT o IntHITtoIntIT) (succ y))).


Compute (((IntITtoIntHIT o IntHITtoIntIT) (succ ((IntITtoIntHIT o IntHITtoIntIT) ( succ y))))).

Context (z : Int).

Compute (IntITtoIntHIT z).

Compute (IntHITtoIntIT (succ y)).



(* pred1 = pred2*)


Definition suc_same
  (z: IntegersHIT)
  : succ ((IntITtoIntHIT o IntHITtoIntIT) z) = succ z.
Proof.
  revert z.
  snrapply IntegersHIT_ind ; cbn beta.
  -
    simpl.
    reflexivity.
  -
    simpl.
    intros.
    apply (ap succ) in X.
    simpl in X.
    (* reflexivity. *)
Abort.

Definition rinv
 (z : IntegersHIT )
 : ((IntITtoIntHIT o IntHITtoIntIT) z) = z.
Proof.
  revert z.
  snrapply IntegersHIT_ind ; cbn beta.
  -
    simpl.
    reflexivity.
  -
    simpl.
    intros z H.
    apply (ap succ) in H.
    simpl in H.
  -

    

    




(* Fixpoint IntITtoIntHIT 
  (z : Int)
  : IntegersHIT
  := match z  with
  | zero => zero_i
  | negS 0 => (pred1 zero_i)
  | negS (S n) => (pred1 (IntITtoIntHIT (negS n)))
  | posS 0 => (succ zero_i)
  | posS (S n) => (succ (IntITtoIntHIT (posS n)))
  end. *)

    (* | negS (S n) => (pred1 (IntITtoIntHIT (negS n))) *)

    (* | posS (S n) => (succ (IntITtoIntHIT (posS n))) *)


  (* apply IntegersHIT_rec Int 0 
   *)


  

  (*1: exact (fun _ => f). *)
(* Abort. *)

(* Definition IntegersHIT_rec *)


(* 
Definition IntegersHIT_rec {P} (c : A -> P) (g : forall a b, R a b -> c a = c b)
  : GraphQuotient R -> P.
Proof.
  srapply GraphQuotient_ind.
  1: exact c.
  intros a b s.
  refine (transport_const _ _ @ g a b s).
Defined. *)





