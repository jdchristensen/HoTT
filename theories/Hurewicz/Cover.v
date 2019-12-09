Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import ReflectiveSubuniverse.
Require Import Modality.

(** O-connected covers *)

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Module Covers (Os : Modalities).
Import Os.
Module Import Os_Theory := Modalities_Theory Os.

  Section Cover.

    Context (O : ReflectiveSubuniverse).

    Global Instance ispointed_O (X : pType)
      : IsPointed (O_reflector O X) := (to O X (point X)).

    Definition pO (X : pType) : pType
      := Build_pType (O_reflector O X) _.

    Definition pto (X : pType) : X ->* pO X
      := Build_pMap X (pO X) (to O X) 1.

    (** O-connected cover *)
    Definition cover (X : pType) : pType
      := pfiber (pto X).

    (** This is why we need O to be a modality rather than just a reflective subuniverse. *)
    Global Instance isconnected_cover (X : pType)
      : IsConnected O (cover X) := _.

    (* The projection map from the O-connected cover to the type. *)
    Definition cover_proj {X : pType} : cover X ->* X
      := Build_pMap (cover X) X pr1 1.

    Global Instance mapinO_cover_proj {X : pType}
      : MapIn O (@cover_proj X) := _.

    Global Instance isequiv_postcompose_cover_proj (* `{Funext} *)
      (X : pType) (Z : pType) `{IsConnected O Z}
      : IsEquiv (fun f : Z ->* _ => @cover_proj X o* f).
    Proof.
      serapply isequiv_adjointify.
      { intro f.
        serapply Build_pMap.
        { 
          intro z.
        
          exists (f z).
          serapply (conn_map_elim O (pto X)).
          intro x.
          unfold IsConnected in H.
          apply path_contr.
    Admitted.

    Definition equiv_cover_corec (X : pType) (Z : pType)
      `{IsConnected O Z} : (Z ->* cover X) <~> (Z ->* X)
      := Build_Equiv _ _ _ (isequiv_postcompose_cover_proj X Z).

  End Cover.

End Covers.