Require Import HoTT.Basics HoTT.Colimits.Pushout.
Require Import Types.Paths Types.Sigma Types.Prod HFiber Limits.Pullback.

(** * Pushouts of "dependent spans". *)

Section SpanPushout.
  Context {X Y : Type} (Q : X -> Y -> Type).

  Definition SPushout := @Pushout@{up _ _ up} (sig@{up _} (fun (xy : X * Y) => Q (fst xy) (snd xy))) X Y
                                  (fst o pr1) (snd o pr1).
  Definition spushl : X -> SPushout := pushl.
  Definition spushr : Y -> SPushout := pushr.
  Definition spglue {x:X} {y:Y} : Q x y -> spushl x = spushr y
    := fun q => pglue ((x,y) ; q).

  Definition spushout_rec (R : Type)
             (spushl' : X -> R) (spushr' : Y -> R)
             (spglue' : forall x y (q : Q x y), spushl' x = spushr' y)
    : SPushout -> R.
  Proof.
    srapply (@Pushout_rec {xy:X * Y & Q (fst xy) (snd xy)} X Y
                          (fst o pr1) (snd o pr1) R spushl' spushr').
    intros [[x y] q]; cbn in *.
    apply spglue'; assumption.
  Defined.
  
  Definition spushout_rec_beta_spglue (R : Type)
             (spushl' : X -> R) (spushr' : Y -> R)
             (spglue' : forall x y (q : Q x y), spushl' x = spushr' y)
             (x:X) (y:Y) (q:Q x y)
    : ap (spushout_rec R spushl' spushr' spglue') (spglue q) = spglue' x y q
    := Pushout_rec_beta_pglue _ _ _ _ ((x, y); q).

  Definition spushout_ind (R : SPushout -> Type)
             (spushl' : forall x, R (spushl x))
             (spushr' : forall y, R (spushr y))
             (spglue' : forall x y (q : Q x y), 
                 transport R (spglue q) (spushl' x) = (spushr' y))
    : forall p, R p.
  Proof.
    srapply (@Pushout_ind {xy:X * Y & Q (fst xy) (snd xy)} X Y
                          (fst o pr1) (snd o pr1) R spushl' spushr').
    intros [[x y] q]; cbn in *.
    apply spglue'; assumption.
  Defined.

  Definition spushout_ind_beta_spglue (R : SPushout -> Type)
             (spushl' : forall x, R (spushl x))
             (spushr' : forall y, R (spushr y))
             (spglue' : forall x y (q : Q x y), 
                 transport R (spglue q) (spushl' x) = (spushr' y))
             (x:X) (y:Y) (q:Q x y)
    : apD (spushout_ind R spushl' spushr' spglue') (spglue q) = spglue'  x y q
    := Pushout_ind_beta_pglue _ _ _ _ ((x,y);q).

End SpanPushout.

Definition functor_spushout {X Y Z W : Type}
  {Q : X -> Y -> Type} {Q' : Z -> W -> Type}
  (f : X -> Z) (g : Y -> W) (h : forall x y, Q x y -> Q' (f x) (g y))
  : SPushout Q -> SPushout Q'.
Proof.
  snapply spushout_rec.
  - exact (fun x => spushl Q' (f x)).
  - exact (fun y => spushr Q' (g y)).
  - intros x y q. apply spglue. exact (h x y q).
Defined.

Definition functor_spushout_compose {X Y X' Y' X'' Y'' : Type}
  {Q : X -> Y -> Type} {Q' : X' -> Y' -> Type} {Q'' : X'' -> Y'' -> Type}
  (f : X -> X') (g : Y -> Y') (f' : X' -> X'') (g' : Y' -> Y'')
  (h : forall x y, Q x y -> Q' (f x) (g y))
  (h' : forall x y, Q' x y -> Q'' (f' x) (g' y))
  : functor_spushout f' g' h' o functor_spushout f g h
    == functor_spushout (f' o f) (g' o g) (fun x y => h' _ _ o h x y).
Proof.
  snapply spushout_ind.
  1,2: reflexivity.
  intros x y q; cbn beta.
  transport_paths FFlFr.
  apply equiv_p1_1q.
  lhs napply ap.
  1: napply spushout_rec_beta_spglue.
  lhs napply spushout_rec_beta_spglue.
  symmetry.
  napply (spushout_rec_beta_spglue Q).
Defined.

Definition functor_spushout_idmap {X Y : Type} {Q : X -> Y -> Type}
  : functor_spushout idmap idmap (fun x y (q : Q x y) => q) == idmap.
Proof.
  snapply spushout_ind.
  1,2: reflexivity.
  intros x y q; cbn.
  transport_paths Flr.
  apply equiv_p1_1q.
  napply spushout_rec_beta_spglue.
Defined.

Definition functor_spushout_homotopic {X Y Z W : Type}
  {Q : X -> Y -> Type} {Q' : Z -> W -> Type}
  {f g : X -> Z} (h : f == g)
  {i j : Y -> W} (k : i == j)
  (l : forall x y, Q x y -> Q' (f x) (i y))
  (m : forall x y, Q x y -> Q' (g x) (j y))
  (H : forall x y q,
    spglue Q' (l x y q) @ ap (spushr Q') (k y)
      = ap (spushl Q') (h x) @ spglue Q' (m x y q))
  : functor_spushout f i l == functor_spushout g j m.
Proof.
  snapply spushout_ind.
  - intros x; cbn.
    exact (ap (spushl Q') (h x)).
  - intros y; cbn.
    exact (ap (spushr Q') (k y)).
  - intros x y q.
    transport_paths FlFr.
    lhs napply whiskerR.
    1: apply spushout_rec_beta_spglue.
    rhs napply whiskerL.
    2: apply spushout_rec_beta_spglue.
    apply H.
Defined.

(** Any pushout is equivalent to a span pushout. *)
Definition equiv_pushout_spushout {X Y Z : Type} (f : X -> Y) (g : X -> Z)
  : Pushout f g
    <~> SPushout (fun (y : Y) (z : Z) => {x : X & f x = y /\ g x = z}).
Proof.
  snapply equiv_pushout.
  { nrefine (equiv_sigma_prod _ oE _).
    apply equiv_double_fibration_replacement. }
  1-4: reflexivity.
Defined.

(** There is a natural map from the total space of [Q] to the pushout product of [Q]. *)
Definition spushout_sjoin_map {X Y : Type} (Q : X -> Y -> Type)
  : {x : X & {y : Y & Q x y}} -> Pullback (spushl Q) (spushr Q)
  := functor_sigma idmap (fun _ => functor_sigma idmap (fun _ => spglue Q)).
