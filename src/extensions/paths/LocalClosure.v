(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)
Set Implicit Arguments.

Require Import Definitions.

(** * Local Closure
  Our definition of [trm] accepts terms that contain de Bruijn indices that are unbound.
  A symbol [X] is considered locally closed, denoted [lc X], if all de Bruijn indices
  in [X] are bound.
   We will require a term to be locally closed in the final safety theorem. *)

(** Only named variables are locally closed. *)
Inductive lc_var : avar -> Prop :=
| lc_var_x : forall x,
    lc_var (avar_f x).

Inductive lc_path : path -> Prop :=
| lc_p: forall x bs,
    lc_var x ->
    lc_path (p_sel x bs).

(** Locally closed types and declarations. *)
Inductive lc_typ : typ -> Prop :=
| lc_typ_top : lc_typ typ_top
| lc_typ_bot : lc_typ typ_bot
| lc_typ_rcd : forall D,
    lc_dec D ->
    lc_typ (typ_rcd D)
| lc_typ_and : forall T1 T2,
    lc_typ T1 ->
    lc_typ T2 ->
    lc_typ (typ_and T1 T2)
| lc_typ_path : forall p L,
    lc_path p ->
    lc_typ (typ_path p L)
| lc_typ_bnd : forall T,
    (forall x, lc_typ (open_typ x T)) ->
    lc_typ (typ_bnd T)
| lc_typ_all : forall T1 T2,
    (forall x, lc_typ (open_typ x T2)) ->
    lc_typ T1 ->
    lc_typ (typ_all T1 T2)
with lc_dec : dec -> Prop :=
| lc_dec_typ : forall A T U,
    lc_typ T ->
    lc_typ U ->
    lc_dec { A >: T <: U }
| lc_dec_trm : forall a T,
    lc_typ T ->
    lc_dec {a ⦂ T}

Hint Constructors lc_var lc_path lc_typ lc_dec.

(*
Scheme lc_trm_mut  := Induction for lc_trm Sort Prop
with   lc_val_mut  := Induction for lc_val Sort Prop
with   lc_def_mut  := Induction for lc_def Sort Prop
with   lc_defs_mut := Induction for lc_defs Sort Prop.
Combined Scheme lc_mutind from lc_trm_mut, lc_val_mut, lc_def_mut, lc_defs_mut.

Scheme lc_typ_mut := Induction for lc_typ Sort Prop
with   lc_dec_mut := Induction for lc_dec Sort Prop.
Combined Scheme lc_typ_mutind from lc_typ_mut, lc_dec_mut.
*)
