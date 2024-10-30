Require Import Basics Types HFiber Modality Truncations.Core.

(** * A Yoneda-like embedding for path types

We prove that [paths : X -> (X -> Type)] is an embedding. This was proved by Escardo as Lemma 15 in "Injective types in univalent mathematics", but we give an argument similar to the proof of Thm 2.25 of CORS. This blog post

  https://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/

has a related argument, but it's for natural transformations, not families of paths. *)

(** TODO: many of these results need to be moved to their natural homes. *)

Definition isequiv_isequiv_compose_embedding {X Y Z : Type}
  {f : X -> Y} (i : Y -> Z) `{IsEmbedding i}
  `{!IsEquiv (i o f)}
  : IsEquiv f.
Proof.
  rapply (cancelL_isequiv i).
  refine (isequiv_surj_emb i).
  rapply (cancelR_issurjection f).
Defined.

(** We characterize the fibers of [functor_forall], but only in the special case where the base map is [idmap]. *)
Definition hfiber_functor_forall_id `{Funext} {A : Type} {P Q : A -> Type}
  (h : forall a, P a -> Q a) (g : forall a, Q a)
  : hfiber (functor_forall_id h) g <~> (forall a, hfiber (h a) (g a)).
Proof.
  unfold hfiber, functor_forall_id, functor_forall.
  nrefine (equiv_sig_coind _ _ oE _).
  apply equiv_functor_sigma_id; intro f.
  apply equiv_apD10.
Defined.

(** Given a family of maps [f : forall a, P a -> Q a] which are in a reflective subuniverse [O], the induced map on Pi types is also in [O]. *)
Definition mapinO_functor_forall_id `{Funext} {O : ReflectiveSubuniverse}
  {A : Type} {P Q : A -> Type} (f : forall a, P a -> Q a) `{forall a, MapIn O (f a)}
  : MapIn O (functor_forall_id f).
Proof.
  intro g.
  rapply (inO_equiv_inO _ (hfiber_functor_forall_id f g)^-1%equiv).
Defined.

(* TODO: Put right after [isequiv_ap_equiv_fun]. *)
(** It follows that [equiv_fun] is an embedding. *)
Global Instance isembedding_equiv_fun `{Funext} {A B : Type}
  : IsEmbedding (@equiv_fun A B).
Proof.
  rapply isembedding_isequiv_ap.
Defined.

(** This will be an inverse to [ap paths].  We'll want to show that it is an embedding, so we'll construct it out of pieces that are clearly equivalences, except for one step, [equiv_fun]. *)
Definition ap_paths_inverse `{Univalence} {X : Type} (x1 x2 : X)
  : paths x1 = paths x2 -> x1 = x2.
Proof.
  refine (_ o @equiv_ap10 _ X Type (paths x1) (paths x2)).
  refine (_ o equiv_functor_forall_id (fun y => equiv_equiv_path (x1 = y) (x2 = y))).
  refine (_ o functor_forall_id (fun y => @equiv_fun (x1 = y) (x2 = y))).
  refine (_ o (equiv_paths_ind x1 (fun y p => x2 = y))^-1%equiv).
  exact (equiv_path_inverse x2 x1).
Defined.

Definition isembedding_paths `{Univalence} {X : Type@{u}} : IsEmbedding (@paths X).
Proof.
  (* To show that [paths] is an embedding, it suffices to show that [ap paths : x1 = x2 -> (paths x1) = (paths x2)] is an equivalence. *)
  snrapply isembedding_isequiv_ap.
  intros x1 x2.
  (* And for that, it suffices to show that [i o (ap paths)] is an equivalence for a well-chosen embedding [i]. *)
  snrapply (isequiv_isequiv_compose_embedding (ap_paths_inverse x1 x2)).
  - (* [ap_paths_inverse x1 x2] is an embedding since it is a composite of four equivalences and one embedding.  We can group these into three parts. *)
    unfold ap_paths_inverse.
    nrefine (mapinO_compose (O:=Tr (-1)) _ (equiv_path_inverse x2 x1 oE _)).
    2: exact _. (* The second part is an equivalence, so it's an embedding. *)
    nrefine (mapinO_compose _ (functor_forall_id _)).
    1: exact _. (* The first part is an equivalence, so it's an embedding. *)
    apply mapinO_functor_forall_id.
    intro y.
    apply isembedding_equiv_fun.
  - (* The composite is an equivalence because it is homotopic to the identity. *)
    simpl.
    srapply (isequiv_homotopic idmap).
    intros [].
    reflexivity.
Defined.
