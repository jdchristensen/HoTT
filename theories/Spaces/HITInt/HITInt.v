Require Import Basics.
Require Import Types.Universe Types.Paths Types.Arrow Types.Sigma Cubical.DPath.
Require Import Spaces.Int.
Require Import Spaces.Nat.Core.
Require Import Equiv.BiInv.

Module Export IntegersHIT.
  Section IntegersHIT.

    Private Inductive IntegersHIT : Type :=
    | zero_i : IntegersHIT
    | succ : IntegersHIT -> IntegersHIT
    | pred1 : IntegersHIT -> IntegersHIT
    | pred2 : IntegersHIT -> IntegersHIT.

    Axiom sec : forall (z : IntegersHIT),
      (pred1 (succ z)) = z.

    Axiom ret : forall (z : IntegersHIT),
      (succ (pred2 z)) = z.

    (* We define the induction principle. We need to use Fixpoint because its recursive*)

    Context {P : IntegersHIT -> Type} {t0 : P zero_i} {f : forall z : IntegersHIT, P z -> P (succ z)}
      {g1 : forall z : IntegersHIT, P z -> P (pred1 z)} {g2 : forall z : IntegersHIT, P z -> P (pred2 z)}
      {s : forall (z : IntegersHIT) (t : P z), (sec z # (g1 (succ z) (f z t)) = t)}
      {r : forall (z : IntegersHIT) (t : P z), (ret z # (f (pred2 z) (g2 z t)) = t)}.

    Fixpoint IntegersHIT_ind
      (x : IntegersHIT) 
      : P x  
      := match x  with
      | zero_i => fun _ _ => t0
      | succ z => fun _ _ =>  f z (IntegersHIT_ind z)
      | pred1 z => fun _ _ =>  g1 z (IntegersHIT_ind z)
      | pred2 z => fun _ _ =>  g2 z (IntegersHIT_ind z)
      end s r.
      (*We make sure that this is dependent on s and r as well*)


    (* we define the beta principles for sec and ret*)

    Axiom IntegersHIT_ind_beta_sec
    : forall (z: IntegersHIT),
      (let f':= IntegersHIT_ind in
      ((apD f' (sec z)) = s z (f' z))).

    Axiom IntegersHIT_ind_beta_ret
    : forall (z: IntegersHIT),
      (let f':= IntegersHIT_ind in
      ((apD f' (ret z)) = r z (f' z))).

  End IntegersHIT.
End IntegersHIT.

Section IntegersHITLemmas.

  Definition IntegersHIT_rec
    (P: Type)
    (t0 : P)
    (f :  P -> P)
    (g1 :  P -> P)
    (g2 :  P -> P)
    (s : forall  (t : P ), (g1 (f t)= t))
    (r : forall  (t : P ), (f (g2 t)= t))
    : IntegersHIT -> P.
  Proof.
    srapply IntegersHIT_ind.
    - exact t0.
    - exact (fun _ => f).
    - exact (fun _ => g1).
    - exact (fun _ => g2).
    - exact (fun z t => (transport_const (sec z) (g1 (f t))) @ (s t)). 
    - exact (fun z t => (transport_const (ret z) (f (g2 t))) @ (r t)).
  Defined.

  Definition IntegersHIT_rec_beta_sec
    (P: Type)
    (t0 : P)
    (f :  P -> P)
    (g1 :  P -> P)
    (g2 :  P -> P)
    (s : forall  (t : P ), (g1 (f t)= t))
    (r : forall  (t : P ), (f (g2 t)= t))
    : forall (z: IntegersHIT),
      (let f':= (IntegersHIT_rec P t0 f g1 g2 s r) in
      ((ap f' (sec z)) = s (f' z))).
  Proof.
  Admitted.

  Definition IntegersHIT_rec_beta_ret
    (P: Type)
    (t0 : P)
    (f :  P -> P)
    (g1 :  P -> P)
    (g2 :  P -> P)
    (s : forall  (t : P ), (g1 (f t)= t))
    (r : forall  (t : P ), (f (g2 t)= t))
    : forall (z: IntegersHIT),
      (let f':= (IntegersHIT_rec P t0 f g1 g2 s r) in
      ((ap f' (ret z)) = r (f' z))).
  Proof.
  Admitted.

  Definition pred1_is_pred2
    (z : IntegersHIT)
    : pred1 z = pred2 z
    := (ap pred1 ((ret z) ^)) @ sec (pred2 z).


  Definition ret_pred1
      (z: IntegersHIT)
      : (succ (pred1 z)) = z.
  Proof.
    intros.
    exact ((ap succ (pred1_is_pred2 z)) @ (ret z)).
  Defined.
End IntegersHITLemmas.

Section IntegersHITEquiv.
    Context {P : Type} {t0 : P} {f :  P -> P} {g1 :  P -> P} {g2 :  P -> P}
    {s : forall  (t : P ), g1 (f t)= t} {r : forall  (t : P ), f (g2 t)= t}.

  Definition IntHITtoIntIT : IntegersHIT -> Int.
  Proof.
    srapply IntegersHIT_rec.
    - exact zero.
    - exact int_succ.
    - exact int_pred.
    - exact int_pred.
    - exact int_succ_pred.
    - exact int_pred_succ.
  Defined.

  Definition IntITtoIntHIT
    (z : Int)
    : IntegersHIT.
  Proof.
    induction z.
    - exact zero_i.
    - exact (succ IHz).
    - exact (pred1 IHz).
  Defined.

  Definition IntITtoIntHIT_is_rinv
  (z : Int )
  : ((IntHITtoIntIT o IntITtoIntHIT) z) = z.
  Proof.
    induction z as [|[|n] IHz|[|n] IHz].  
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - apply (ap int_succ) in IHz.
      apply IHz. 
    - simpl.
      reflexivity.
    - simpl.
      apply (ap int_pred) in IHz.
      apply IHz.
  Defined.

  Definition left_inverse_compatible
    (k: IntegersHIT -> P)
    (p0 : (k zero_i) = t0)
    (pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
      : forall  (z : IntegersHIT), (g1 o k) z = (k o pred1) z.
  Proof.
    intros.
    exact ((s (k(pred1 z)))^ @ (ap g1 (pf (pred1 z))) 
          @ (ap (g1 o k) (ret_pred1 z)))^ .
  Defined.

  Definition right_inverse_compatible
    (k: IntegersHIT -> P)
    (p0 : (k zero_i) = t0)
    (pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
      : forall  (z : IntegersHIT), (g2 o k) z = (k o pred2) z.
  Proof.
    intros.
    exact (((s (g2 (k z)))^ @ (ap g1 (r (k z)))) @ ((s (k (pred2 z)))^ 
          @ (ap g1 (pf (pred2  z))) @ (ap (g1 o k) (ret z)))^).
  Defined.

  (* With these lemmas, we can prove a uniqueness principle for for maps into sets.*)

  Definition uniquenessZset
    (v : IsHSet P)
    (k: IntegersHIT -> P)
    (p0 : (k zero_i) = t0)
    (pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
    : forall (z : IntegersHIT), k z = (IntegersHIT_rec P t0 f g1 g2 s r) z.
    Proof.
    snrapply IntegersHIT_ind.
    - simpl.
      exact p0.
    - simpl.
      intros z H.
      apply (ap f) in H.
      exact (((pf z)^) @ H).
    - simpl.
      intros z H.
      apply (ap g1) in H.
      exact ((((left_inverse_compatible k p0 pf) z)^) @ H).
    - simpl.
      intros z H.
      apply (ap g2) in H.
      exact ((((right_inverse_compatible k p0 pf) z)^) @ H).
    - simpl.
      intros.
      rapply path_ishprop.
    - simpl. 
      intros.
      rapply path_ishprop.
  Defined.

End IntegersHITEquiv.


(* END OF THE PART THAT IS COMPLETED*)
(* ----------------------------------------------------------------------------*)

(* The subsequent section contains incomplete proofs I am currently working on. I included them to show the work in progress.*)


(* for some reason we need to make the implicit arguments explicit at several places in the following lemmas*)
Definition compatibility_sec
  (P: Type)
  (t0 : P)
  (f :  P -> P)
  (g1 :  P -> P)
  (g2 :  P -> P)
  (s : forall  (t : P ), (g1 (f t)= t))
  (r : forall  (t : P ), (f (g2 t)= t))
  (k: IntegersHIT -> P)
  (p0 : (k zero_i) = t0)
  (pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
    : forall  (z : IntegersHIT), s (k z) = (ap g1 (pf z)) 
      @ ((left_inverse_compatible (s := s) k p0 pf) (succ z)) @ (ap k (sec z)).
Proof.
  (*TODO: The proof of this will be established once the equivalence induction principle for bi-invertible maps is done*)
Abort.

Definition compatibility_ret
  (P: Type)
  (t0 : P)
  (f :  P -> P)
  (g1 :  P -> P)
  (g2 :  P -> P)
  (s : forall  (t : P ), (g1 (f t)= t))
  (r : forall  (t : P ), (f (g2 t)= t))
  (k: IntegersHIT -> P)
  (p0 : (k zero_i) = t0)
  (pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
    : forall  (z : IntegersHIT), r (k z) 
    = (ap f ((right_inverse_compatible (P := P) (t0 := t0) (f := f) (g1 := g1) (g2 := g2) (s := s) (r := r) k p0 pf) z)) 
        @ (pf (pred2 z)) @ (ap k (ret z)).
Proof.
  (*TODO: The proof of this will be established once the equivalence induction principle for bi-invertible maps is done*)
Abort.


(*The following general uniqueness prenciple relies on the two preceeding lemmas.*)

Definition uniquenessZ
  (P: Type)
  (t0 : P)
  (f :  P -> P)
  (g1 :  P -> P)
  (g2 :  P -> P)
  (s : forall  (t : P ), (g1 (f t)= t))
  (r : forall  (t : P ), (f (g2 t)= t))
  (k: IntegersHIT -> P)
  (p0 : (k zero_i) = t0)
  (pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
  : forall (z : IntegersHIT), k z = (IntegersHIT_rec P t0 f g1 g2 s r) z.
  Proof.
  snrapply IntegersHIT_ind.
  - simpl.
    exact p0.
  - simpl.
    intros.
    apply (ap f) in X. (*give it a name*)
    exact (((pf z)^) @ X).
  - simpl.
    intros z H.
    apply (ap g1) in H.
    exact ((((left_inverse_compatible (s := s) k p0 pf) z)^) @ H).
  - simpl.
    intros z H.
    apply (ap g2) in H.
    exact ((((right_inverse_compatible (P := P) (t0 := t0) (f := f) (g1 := g1) (g2 := g2) (s := s) (r := r) k p0 pf) z)^) @ H).
  - simpl.
    intros.
    (* TODO *)
    (* Here and in the next goal the preceeding lemmas should be used, once they are proved.*)
Abort.


(* The idea is to approach the two lemmas above by deriving first an equivalence induction principle for biinvertible maps.
We use BiInv from BiInv.v. We will need however some further stuff that is not in the file such as a record for biinvertible maps.*)

Generalizable Variables A B C D f.


(* Here are some projections *)
Definition ret_binv `(f : A -> B)
  : BiInv f ->  (B -> A).
  intro.
  exact (pr1 (fst X)).
Defined.

Definition sec_binv `(f : A -> B)
  : BiInv f ->  (B -> A).
  intro.
  exact (pr1 (snd X)).
Defined.

Check sec_binv.

Definition isret_binv `(f : A -> B)
  : forall (e: BiInv f), f o (sec_binv f e)   == idmap.
  intro.
  simpl.
  exact (pr2 (snd e)).
Defined.

Definition issec_binv `(f : A -> B)
  : forall (e: BiInv f), (ret_binv f e) o f   == idmap.
  intro.
  simpl.
  exact (pr2 (fst e)).
Defined.


Record EquivBiInv A B := {
  equiv_fun_binv :> A -> B ;
  equiv_isequiv_binv : BiInv equiv_fun_binv
}.

Definition issig_equivbiinv (A B : Type)
  : {f : A -> B & BiInv f} <~> EquivBiInv A B.
Proof.
  issig.
Defined.

(* Some lemmas to send equivalences and biinvertible maps back and forth.*)

Definition isequiv_biinv_record A B
  : EquivBiInv A B -> A <~> B.
Proof.
  intros [f e].
  exact (Build_Equiv A B f (isequiv_biinv f e)).
Defined.

Definition biinv_isequiv_record A B
  :  A <~> B -> EquivBiInv A B.
Proof.
  intros [f e].
  exact (Build_EquivBiInv A B f (biinv_isequiv f e)).
Defined.

Definition iff_biinv_isequiv_record A B
  : EquivBiInv A B <-> A <~> B.
Proof.
  split.
  - apply isequiv_biinv_record.
  - apply biinv_isequiv_record.
Defined.

Definition equiv_biinv_isequiv_record `{Funext} A B
  : EquivBiInv A B <~> (A <~> B) .
Proof.
  refine ((issig_equiv A B) oE _ oE (issig_equivbiinv A B)^-1).
  rapply (equiv_functor_sigma_id equiv_biinv_isequiv).
Defined.

Context `{Univalence}.

Definition equiv_path_binv (A B : Type@{u}) (p : A = B) : EquivBiInv A B 
  := (((equiv_fun (equiv_biinv_isequiv_record A B)^-1) o (equiv_path A B)) p).

(* TODO: The following should be derivable from equiv_path being an equivalence using univalence. It should NOT be an extra axiom.*)
Axiom isequiv_equiv_path_binv : forall `{Univalence} (A B : Type@{u}), IsEquiv (equiv_path_binv A B).
Global Existing Instance isequiv_equiv_path_binv.



(* To get our equivalence induction principle for biinvertible maps we define the following variant of equiv_ind *)

Definition equiv_ind_binv `(e: BiInv (f : A -> B))  (P : B -> Type)
  : (forall x:A, P (f x)) -> forall y:B, P y
  := fun g y => transport P ((proj2 (snd e)) y) (g (proj1 (snd e) y)).

Arguments equiv_ind_binv {A B} f {_} P _ _.

(* The following gives for each type trivial biinvertible map. This can be made cleaner by defining it directly.*)
(* Definition equiv_idmap_binv (A : Type) : (EquivBiInv A A) 
    := Build_EquivBiInv A A (equiv_fun (equiv_idmap A)) (biinv_isequiv (equiv_fun (equiv_idmap A)) (equiv_isequiv (equiv_idmap A))). *)

Definition equiv_idmap_binv (A : Type) 
  : (EquivBiInv A A).
Proof.
  snrapply (Build_EquivBiInv A A).
  - exact idmap.
  -
    snrapply pair.
    -- snrapply exist.
       --- exact idmap.
       --- simpl.
           reflexivity. 
    -- snrapply exist.
       --- exact idmap.
       --- simpl.
           reflexivity.
Defined.

(** A typeclass that includes the data making [f] into a bi-invertible equivalence. *)
Class IsBinv {A B : Type} (f : A -> B) := {
  sec_proj : B -> A ;
  ret_proj : B -> A ;
  eisretr : f o sec_proj == idmap ;
  eissect : ret_proj o f == idmap ;
}.


Record EquivBiInv_record A B := {
  equiv_fun_binv' : A -> B ;
  equiv_isequiv_binv' : IsBinv equiv_fun_binv'
}.


(* Search prod. *)

(* Check Build_prod. *)



Definition equiv_idmap_binv_record (A : Type) 
  : (EquivBiInv_record A A).
Proof.
  snrapply Build_EquivBiInv_record.
  - exact idmap.
  - snrapply Build_IsBinv.
    -- exact idmap.
    -- exact idmap.
    -- simpl.
       reflexivity.
    -- simpl.
       reflexivity.
Defined.   

    (* := Build_EquivBiInv' A A idmap (Build_IsBinv A A idmap idmap idmap idpath idpath). *)


(* Print equiv_idmap_binv. *)

(** The equivalence induction principle*)
(** Paulin-Mohring style *)
Theorem equiv_induction_binv {U : Type} (P : forall V, EquivBiInv U V -> Type)
  : (P U (equiv_idmap_binv U)) -> (forall V (w :  EquivBiInv U V), P V w).
Proof.
  intros H0 V w.
  snrapply (equiv_ind_binv (equiv_path_binv U V)).
  - apply equiv_biinv_isequiv.
    apply isequiv_equiv_path_binv.
  - intro p.
    induction p.
    exact H0.
Defined.


(** Martin-Lof style *)
Theorem equiv_induction_binv' 
  (P : forall U V, (EquivBiInv U V) -> Type)
  : (forall T, P T T (equiv_idmap_binv T)) -> (forall U V (w : (EquivBiInv U V)), P U V w).
Proof.
  intros H0 U V w.
  snrapply (equiv_ind_binv (equiv_path_binv U V)). 
  - apply equiv_biinv_isequiv.
    apply isequiv_equiv_path_binv.
  - intro p.
    induction p.
    apply H0.
Defined.




(* 
Definition compatibility_sec2
  (P: Type)
  (t0 : P)
  (* (f :  P -> P)
  (g1 :  P -> P)
  (g2 :  P -> P)
  (s : forall  (t : P ), (g1 (f t)= t))
  (r : forall  (t : P ), (f (g2 t)= t))  *)
  (e: EquivBiInv P P)
  (k: IntegersHIT -> P)
  (p0 : (k zero_i) = t0)
  (pf : forall (z : IntegersHIT), ((equiv_fun_binv P P e) o k) z = (k o succ) z)
    : forall  (z : IntegersHIT), (pr2 (fst (equiv_isequiv_binv P P e))) (k z) 
    = (ap (pr1 (fst (equiv_isequiv_binv P P e))) (pf z)) 
    @ ((left_inverse_compatible (f := (equiv_fun_binv P P e)) (g1 := (proj1 (fst (equiv_isequiv_binv P P e)))) (s := (proj2 (fst (equiv_isequiv_binv P P e))))  k p0 pf) (succ z)) @ (ap k (sec z)).
Proof.
  intro.
  simpl.
  generalize dependent e.
  snrapply equiv_induction_binv.

  (* snrapply (equiv_induction_binv (U := P)). *)
  (*TODO: The proof of this will be established once the equivalence induction principle for bi-invertible maps is done*)
Abort. *)


(*(r := (proj2 (snd (equiv_isequiv_binv P P e))))*)
(*(g2 := (proj1 (snd (equiv_isequiv_binv P P e))))*)


Record prBiInv A B C D (e: EquivBiInv A B) (e' : EquivBiInv C D) (a: A -> C) (b: B -> D)
  := {
  pe : forall (x : A), ((equiv_fun_binv C D e') o a) x = (b o (equiv_fun_binv A B e)) x;
  pg : forall (y : B), ((ret_binv (equiv_fun_binv C D e') (equiv_isequiv_binv C D e')) o b) y = (a o (ret_binv (equiv_fun_binv A B e) (equiv_isequiv_binv A B e))) y;
  ph : forall (y : B), ((sec_binv (equiv_fun_binv C D e') (equiv_isequiv_binv C D e')) o b) y = (a o (sec_binv (equiv_fun_binv A B e) (equiv_isequiv_binv A B e))) y;
  ps : forall (x: A), (issec_binv (equiv_fun_binv C D e') (equiv_isequiv_binv C D e') (a x)) = ((ap (ret_binv (equiv_fun_binv C D e') (equiv_isequiv_binv C D e')) (pe x)) @ (pg ((equiv_fun_binv A B e) x)) @ (ap a (issec_binv (equiv_fun_binv A B e) (equiv_isequiv_binv A B e) x) ));
  pr : forall (y: B), (isret_binv (equiv_fun_binv C D e') (equiv_isequiv_binv C D e') (b y)) = ((ap (equiv_fun_binv C D e') (ph y)) @ (pe (sec_binv (equiv_fun_binv A B e) (equiv_isequiv_binv A B e) y)) @ (ap b (isret_binv (equiv_fun_binv A B e) (equiv_isequiv_binv A B e) y) ));
}.

Check prBiInv.

Search prBiInv.

(* Definition cancel
  (A: Type)
  (x y :A)
  (p : x = y)
  :
   1 = (ap idmap (p @ p^)) @ 1.
  Proof.
  induction p.
  simpl.
  reflexivity.
Defined. *)

Definition cancel
  (A: Type)
  (x y :A)
  (p : x = y)
  :
   1 = (ap idmap (p^)) @ p @ 1.
  Proof.
  induction p.
  simpl.
  reflexivity.
Defined.

Context {K : Type}.

Compute issec_binv idmap ((idmap; fun x0 : K => 1), (idmap; fun x0 : K => 1)).

Definition compat_implies_prBiInv
  (A B C D: Type)
  (e: EquivBiInv A B)
  (e':  EquivBiInv C D)
  (a: A -> C)
  (b : B -> D)
  :
    (forall (x : A), (e' o a) x = (b o e) x) -> prBiInv A B C D e e' a b.
Proof.
  revert b.  
  generalize dependent e.
  revert B.
  snrapply equiv_induction_binv.
  generalize dependent e'.
  revert D.
  snrapply equiv_induction_binv.
  simpl.
  intros b H.
  snrapply Build_prBiInv.
  - simpl.
    exact H.
  - 
    intro y.
    simpl.
    exact (H y)^.
  -
    intro y.
    simpl. 
    exact (H y)^.
  -
    simpl.
    intro x.
    induction (H x).
    reflexivity.
  -
    simpl.
    intro y.
    simpl.
    exact (cancel C (a y) (b y) (H y)). (*There is a bug somewhere, this cannot be resolved by doing induction (X y) *)
Defined.

Definition integershit_to_biinv
    : EquivBiInv IntegersHIT IntegersHIT.
Proof.
  snrapply Build_EquivBiInv.
  - exact succ.
  - snrapply pair.
    -- snrapply exist.
       --- exact pred1.
       --- exact sec.
    -- snrapply exist.
       --- exact pred2.
       --- exact ret.
Defined.

Section Test.

Context {P : Type} {e: EquivBiInv P P}.

Local Definition f := (equiv_fun_binv P P e).
Local Definition g1 := (ret_binv f (equiv_isequiv_binv P P e)).
Local Definition g2 := (sec_binv f (equiv_isequiv_binv P P e)).
Local Definition s := (issec_binv f (equiv_isequiv_binv P P e) ).
Local Definition r := (isret_binv f (equiv_isequiv_binv P P e) ).


(* Compute ap (IntegersHIT_rec P t0 f g1 g2 s r) (sec z).

Compute (IntegersHIT_ind_beta_sec P t0 f g1 g2 s r). *)

(* 
Definition inv_pp' {A : Type} {x y z w : A} (p : x = y) (q : y = z) (r: z = w):
  r^ @ (q^ @ p^) = (p @ q @ r)^.
  Proof.
  induction r.
  induction q.
  induction p.
  reflexivity.
Defined.

Definition inv_pp'' {A : Type} {x y z : A} (p : x = y) (q : y = z):
  q^ @ p^ = (p @ q )^.
  Proof.
  induction q.
  induction p.
  reflexivity.
Defined. *)


(* ((ap k (sec z))^ @
((pg IntegersHIT IntegersHIT P P integershit_to_biinv e k k compat
(succ z))^ @ (ap g1 (pf z)^ @ ap g1 (ap f t)))) @ ap rec
(sec z) =
t *)

(* Check ret_binv e. *)

Definition uniquenessZ
  (t0 : P)
  (k: IntegersHIT -> P)
  (p0 : (k zero_i) = t0)
  (pf : forall (z : IntegersHIT), (f o k) z = (k o succ) z)
  (* (x := sgdshj) *)
  (rec := IntegersHIT_rec P t0 f g1 g2 s r)
  (compat := compat_implies_prBiInv _ _ _ _ integershit_to_biinv e k k pf)
  : forall (z : IntegersHIT), k z = rec z.
  Proof.
  snrapply IntegersHIT_ind.
  - simpl.
    exact p0.
  - simpl.
    intros z H.
    apply (ap f) in H. 
    (* exact (((pf z)^) @ H). *)
    exact (((pe _ _ _ _ _ _ _ _ compat z)^) @ H).
  - simpl.
    intros z H.
    apply (ap g1) in H.
    exact (((pg _ _ _ _ _ _ _ _ compat z)^) @ H).
  - intros z H.
    apply (ap g2) in H.
    exact (((ph _ _ _ _ _ _ _ _ compat z)^) @ H).
  - simpl.
    intros z t.
    rewrite transport_paths_FlFr.
    rewrite ap_pp.
    rewrite concat_p_pp.
    (* rewrite concat_p_pp. *)
    (* rewrite inv_pp. *)
    rewrite (inv_pp _ _)^.
    rewrite concat_p_pp.
    rewrite ap_V.
    rewrite (inv_pp _ _)^.
    (* rewrite (concat_p_pp _ _ _)^. *)
    (* rewrite concat_p_pp. *)
    rewrite concat_p_pp.
    rewrite (ps _ _ _ _ _ _ _ _ compat z)^.
    rewrite (concat_p_pp _ _ _)^.
    apply moveR_Vp.
    rewrite (ap_compose _ _ _)^.
    rewrite IntegersHIT_rec_beta_sec.
    apply (concat_A1p (f := g1 o e)).
  - simpl.
    intros z t.
    rewrite transport_paths_FlFr.
    rewrite ap_pp.
    rewrite concat_p_pp.
    (* rewrite concat_p_pp. *)
    (* rewrite inv_pp. *)
    rewrite (inv_pp _ _)^.
    rewrite concat_p_pp.
    rewrite ap_V.
    rewrite (inv_pp _ _)^.
    (* rewrite (concat_p_pp _ _ _)^. *)
    (* rewrite concat_p_pp. *)
    rewrite concat_p_pp.
    rewrite (pr _ _ _ _ _ _ _ _ compat z)^.
    rewrite (concat_p_pp _ _ _)^.
    apply moveR_Vp.
    rewrite (ap_compose _ _ _)^.
    rewrite IntegersHIT_rec_beta_ret.
    apply (concat_A1p (f := f o g2)).
Defined.



    (* .
    rewrite moveL_Mp. *)


    exact ((ps _ _ _ _ _ _ _ _ compat z)^).
    exact (concat_A1p (A := P) (f := (g1 o f)) s (x := (k z)) (y := rec(z)) t).
    (* exact ((ps _ _ _ _ _ _ _ _ (compat_implies_prBiInv _ _ _ _ integershit_to_biinv e k k pf) z)). *)
Admitted.


End Test.


Definition IntITtoIntHIT_comp_succ
  (z: Int)
  : succ (IntITtoIntHIT z) = IntITtoIntHIT ( int_succ z).
  simpl.
  induction z as [|[|n] IHz|[|n] IHz].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    exact (ret_pred1 zero_i).
  - simpl.
    exact ((ret_pred1 _)).
Defined.

Definition IntITtoIntHIT_comp_succ'
  (z: IntegersHIT)
  : succ (IntITtoIntHIT ( IntHITtoIntIT z)) = IntITtoIntHIT ( IntHITtoIntIT  (succ z)).
  simpl.
  exact ((IntITtoIntHIT_comp_succ o IntHITtoIntIT) z).
Defined.

Definition IntITtoIntHIT_is_linv_lemma_zero :
  IntITtoIntHIT (IntHITtoIntIT zero_i) = zero_i.
  Proof.
    simpl.
    reflexivity.
Defined.


Definition IntITtoIntHIT_is_linv_comp_idmap
  (z: IntegersHIT)
  : succ (idmap z) = idmap  ( succ z).
  Proof.
    simpl.
    reflexivity.
Defined.

Definition IntITtoIntHIT_is_linv_lemma_idmap':
  idmap zero_i = zero_i.
  Proof.
    simpl.
    reflexivity.
Defined.

Definition IntITtoIntHIT_is_linv
 (z : IntegersHIT )
 : (( IntITtoIntHIT o IntHITtoIntIT) z) = z.
Proof.
  exact (((uniquenessZ (P := IntegersHIT) (e := integershit_to_biinv) zero_i (IntITtoIntHIT o IntHITtoIntIT)  IntITtoIntHIT_is_linv_lemma_zero IntITtoIntHIT_comp_succ') z) 
  @ ((uniquenessZ (P := IntegersHIT) (e := integershit_to_biinv) zero_i idmap IntITtoIntHIT_is_linv_lemma_idmap' IntITtoIntHIT_is_linv_comp_idmap) z)^).
Defined.



(*   
  - simpl.
    exact p0.
  - simpl.
    intros.
    apply (ap f) in X. (*give it a name*)
    exact (((pf z)^) @ X).
  - simpl.
    intros z H.
    apply (ap g1) in H.
    exact ((((left_inverse_compatible (s := s) k p0 pf) z)^) @ H).
  - simpl.
    intros z H.
    apply (ap g2) in H.
    exact ((((right_inverse_compatible (P := P) (t0 := t0) (f := f) (g1 := g1) (g2 := g2) (s := s) (r := r) k p0 pf) z)^) @ H).
  - simpl.
    intros.

    (* TODO *)
    (* Here and in the next goal the preceeding lemmas should be used, once they are proved.*)
Abort. *)


















    (* exact (issec_binv idmap ((idmap; fun x0 : C => 1), (idmap; fun x0 : C => 1)) (a x) = (ap (ret_binv idmap ((idmap; fun x0 : C => 1), (idmap; fun x0 : C => 1))) (X x) @ (X x)^) @ 1)
    (* reflexivity. *)
    exact (cancel C (a x) (b x) (X x)).

  reflexivity. *)



  revert pe.
  revert b.  
  generalize dependent e.
  revert B.

  (* generalize dependent e'. *)












Compute IntITtoIntHIT (negS 5).

Compute IntITtoIntHIT (posS 2).




Compute IntITtoIntHIT (posS 5).

Compute IntITtoIntHIT (negS 1).

Compute IntITtoIntHIT zero. 

Compute IntHITtoIntIT zero_i.

Compute IntHITtoIntIT (succ (pred2 zero_i)).

Compute IntHITtoIntIT (pred1 (succ (pred2 zero_i))).

Compute IntHITtoIntIT (succ (succ (succ zero_i))).

Compute IntHITtoIntIT (succ (succ zero_i)).


Check IntegersHIT_ind.
  About IntegersHIT_ind.
  Check transport_const.
Check IntegersHIT_ind.







Print equiv_induction.






Check Build_EquivBiInv.




(* Context A B (e : EquivBiInv A B).

Compute (biinv_isequiv_record A B o isequiv_biinv_record A B) e.

Context C D (f : C <~> D).

Compute (isequiv_biinv_record  C D o biinv_isequiv_record C D) f. *)



Definition equiv_biinv_isequiv_record A B
  : BiInv (isequiv_biinv_record A B).
Proof.
    simpl.
    split.
    -
      (* exact (biinv_isequiv_record A B). *)
      exact (biinv_isequiv_record A B, fun _  => reflexivity).
    exact {|equiv_fun_binv := isequiv_biinv_record|}.


Definition equiv_biinv_isequiv_record A B
  :EquivBiInv A B <~> (A <~> B).
Proof.
  simpl.
  (* split. *)
  symmetry.
  exact (Build_Equiv _ _ (biinv_isequiv_record A B) {|equiv_inv := (isequiv_biinv_record A B); eisretr := |} ).
  apply iff_biinv_isequiv_record.
Abort.






(* Definition half :=
  {| equiv_fun_binv := false;
     Rat_bottom_nonzero := O_S 1;
     Rat_irreducible := one_two_irred |}. *)



Check equiv_idmap_binv.




Check equiv_path.








(*Lemma 12 is just equivalence induction*)
(* How to do equivalence induction*)
(*EquivalenceInduction.v*)
(*Basics/Equivalence.v Lemma equiv_ind. Tyoe family over B and equivalence f A to B and with substitution the original. and apply it to univalence which is an equivalence. Look at 'equiv_induction' in Universe.v Redo this for for biinvertible maps*)
(* Univalence is in the context Context `{Univalence}`*)

(* One other idea is to show its a set show it has decideable equality then there is lemma*)
(* for every two elements either they are equal or a proof that they are equal*)
(*nat uses encode decode*)
(* check out integers how its done there*)


(* 
Definition is_set_IntegersHIT
  (x : IntegersHIT ) 
  (y : IntegersHIT ) 
  (p: x = y)
  (q: x = y)
  : p = q.
  Proof.
    intros.
    snrapply IntegersHIT_ind.
    (* snrapply IntegersHIT_ind (@...) *)
Abort.     *)

(* 
Definition IntITtoIntHIT_is_linv
 (z : Int )
 : ((IntITtoIntHIT o IntHITtoIntIT ) z) = z.
Proof.

Abort. *)


(*we can define some basic arithmetic stuff*)
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





























(*     
    exact (l (k z) (IntegersHIT_rec P t0 f g1 g2 s r z) (transport (fun x : IntegersHIT => k x = IntegersHIT_rec P t0 f g1 g2 s r x)
  (ret z) ((pf (pred2 z))^ @ ap f (((right_inverse_compatible P t0 f g1 g2 s r k p0 pf) z)^ @ ap g2 t))) t). *)
(* exact (l (k z)  (IntegersHIT_rec P t0 f g1 g2 s r z) (transport (fun x : IntegersHIT => k x = IntegersHIT_rec P t0 f g1 g2 s r x)
  (sec z) (((left_inverse_compatible P t0 f g1 g2 s r k p0 pf) (succ z))^ @ ap g1 ((pf z)^ @ ap f t))) t). *)



(* Definition is_set_IntegersHIT
  : forall (x : IntegersHIT) (p: x = x), p = idpath.
  Proof.
    intros.
    revert p.
    snrapply IntegersHIT_ind. *)


(* first mapping to set*)
(* 
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
Defined. *)


(* 
    exact (l z _ _ (transport_const (sec z) ((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t))) t).
    exact (fun z t => l z _ _ (transport_const (sec z) ((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t))) t).
    exact (fun z t => (transport_const (sec z) (l z _ _ (ap (sec z) t) (((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t)))))).

    exact (l z (k z) (IntegersHIT_rec P t0 f g1 g2 s r z) (t) (transport_const (sec z)  ((pg1 (succ z))^ @ ap g1 ((pf z)^ @ ap f t)))).

 *)


(* Definition uniquenessZ
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
}.  *)





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





