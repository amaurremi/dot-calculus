(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [⊢##] and [ty_val_inv], [⊢##v]). *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Definitions.
Require Import PreciseTyping.

(** * Tight typing [G |-# t: T] *)

Reserved Notation "G '⋆' Sigma '⊢#' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '⋆' Sigma '⊢#' T '<:' U" (at level 40, T at level 59).

(** *** Tight term typing [G ⋆ Sigma ⊢# t: T] *)
(** Tight typing is very similar to general typing, and could be obtained by replacing
    all occurrences of [⊢] with [⊢#], except for the following:
    - in the type selection subtyping rules Sel-<: and <:-Sel ([subtyp_sel1] and [subtyp_sel2]),
      the premise is precise typing of a type declaration with equal bounds;
    - whenever a typing judgement in a premise extends the environment (for example, [ty_all_intro_t]),
      it is typed under general typing [⊢] and not tight typing [⊢#]. *)

Inductive ty_trm_t : ctx -> stoty -> trm -> typ -> Prop :=

(** [G(x) = T]   #<br>#
    [――――――――――] #<br>#
    [G ⋆ Sigma ⊢# x: T]  *)
| ty_var_t : forall G Sigma x T,
    binds x T G ->
    G ⋆ Sigma ⊢# trm_var (avar_f x) : T

(** [Sigma(l) = T]      #<br>#
    [―――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# l: T] *)
| ty_loc : forall G Sigma l T,
    binds l T Sigma ->
    G ⋆ Sigma ⊢# trm_val (val_loc l) : (typ_ref T)

(** [G, x: T ⋆ Sigma ⊢ t^x: U^x]       #<br>#
    [x fresh]                  #<br>#
    [――――――――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# lambda(T)t: forall(T)U]     *)
| ty_all_intro_t : forall L G Sigma T t U,
    (forall x, x \notin L ->
      G & x ~ T ⋆ Sigma ⊢ open_trm x t : open_typ x U) ->
    G ⋆ Sigma ⊢# trm_val (val_lambda T t) : typ_all T U

(** [G ⋆ Sigma ⊢# x: forall(Sigma)T] #<br>#
    [G ⋆ Sigma ⊢# z: S]     #<br>#
    [――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# x z: T^z]     *)
| ty_all_elim_t : forall G Sigma x z T U,
    G ⋆ Sigma ⊢# trm_var (avar_f x) : typ_all T U ->
    G ⋆ Sigma ⊢# trm_var (avar_f z) : T ->
    G ⋆ Sigma ⊢# trm_app (avar_f x) (avar_f z) : open_typ z U

(** [G, x: T^x ⋆ Sigma ⊢ ds^x :: T^x]    #<br>#
    [x fresh]                    #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [G ⋆ Sigma ⊢# nu(T)ds :: mu(T)]         *)
| ty_new_intro_t : forall L G Sigma T ds,
    (forall x, x \notin L ->
      G & (x ~ open_typ x T) ⋆ Sigma /- open_defs x ds :: open_typ x T) ->
    G ⋆ Sigma ⊢# trm_val (val_new T ds) : typ_bnd T

(** [G ⋆ Sigma ⊢# x: {a: T}] #<br>#
    [―――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# x.a: T]        *)
| ty_new_elim_t : forall G Sigma x a T,
    G ⋆ Sigma ⊢# trm_var (avar_f x) : typ_rcd (dec_trm a T) ->
    G ⋆ Sigma ⊢# trm_sel (avar_f x) a : T

(** [G ⋆ Sigma ⊢# t: T]             #<br>#
    [G, x: T ⋆ Sigma ⊢ u^x: U]       #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――]       #<br>#
    [G ⋆ Sigma ⊢# let t in u: U]        *)
| ty_let_t : forall L G Sigma t u T U,
    G ⋆ Sigma ⊢# t : T ->
    (forall x, x \notin L ->
      G & x ~ T ⋆ Sigma ⊢ open_trm x u : U) ->
    G ⋆ Sigma ⊢# trm_let t u : U

(** [G ⋆ Sigma ⊢# x: T^x]   #<br>#
    [――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# x: mu(T)] *)
| ty_rec_intro_t : forall G Sigma x T,
    G ⋆ Sigma ⊢# trm_var (avar_f x) : open_typ x T ->
    G ⋆ Sigma ⊢# trm_var (avar_f x) : typ_bnd T

(** [G ⋆ Sigma ⊢# x: mu(T)] #<br>#
    [――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# x: T^x]       *)
| ty_rec_elim_t : forall G Sigma x T,
    G ⋆ Sigma ⊢# trm_var (avar_f x) : typ_bnd T ->
    G ⋆ Sigma ⊢# trm_var (avar_f x) : open_typ x T

(** [G ⋆ Sigma ⊢# x: T]      #<br>#
    [G ⋆ Sigma ⊢# x: U]      #<br>#
    [―――――――――――――]   #<br>#
    [G ⋆ Sigma ⊢# x: T /\ U]      *)
| ty_and_intro_t : forall G Sigma x T U,
    G ⋆ Sigma ⊢# trm_var (avar_f x) : T ->
    G ⋆ Sigma ⊢# trm_var (avar_f x) : U ->
    G ⋆ Sigma ⊢# trm_var (avar_f x) : typ_and T U

(** [G ⋆ Sigma ⊢# t: T]    #<br>#
    [G ⋆ Sigma ⊢# T <: U]  #<br>#
    [―――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# t: U]        *)
| ty_sub_t : forall G Sigma t T U,
    G ⋆ Sigma ⊢# t : T ->
    G ⋆ Sigma ⊢# T <: U ->
    G ⋆ Sigma ⊢# t : U

(** [G ⋆ Sigma ⊢# x: T]             #<br>#
    [―――――――――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# ref x T : Ref T ] *)
| ty_ref_intro : forall G Sigma x T,
    G ⋆ Sigma ⊢# trm_var (avar_f x) : T ->
    G ⋆ Sigma ⊢# (trm_ref (avar_f x) T) : typ_ref T

(** [G ⋆ Sigma ⊢# x : Ref T ] #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# !x : T ] *)
| ty_ref_elim : forall G Sigma x T,
    G ⋆ Sigma ⊢# trm_var (avar_f x) : typ_ref T ->
    G ⋆ Sigma ⊢# trm_deref (avar_f x) : T

(** [G ⋆ Sigma ⊢# x : Ref T ]  #<br>#
    [G ⋆ Sigma ⊢# y : T ]      #<br>#
    [――――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# x := y : T ] *)
| ty_asgn : forall G Sigma x y T,
    G ⋆ Sigma ⊢# trm_var (avar_f x) : typ_ref T ->
    G ⋆ Sigma ⊢# trm_var (avar_f y) : T ->
    G ⋆ Sigma ⊢# trm_asg (avar_f x) (avar_f y) : T
where "G '⋆' Sigma '⊢#' t ':' T" := (ty_trm_t G Sigma t T)

(** *** Tight subtyping [G ⋆ Sigma ⊢# T <: U] *)
with subtyp_t : ctx -> stoty -> typ -> typ -> Prop :=

(** [G ⋆ Sigma ⊢# T <: top] *)
| subtyp_top_t: forall G Sigma T,
    G ⋆ Sigma ⊢# T <: typ_top

(** [G ⋆ Sigma ⊢# bot <: T] *)
| subtyp_bot_t: forall G Sigma T,
    G ⋆ Sigma ⊢# typ_bot <: T

(** [G ⋆ Sigma ⊢# T <: T] *)
| subtyp_refl_t: forall G Sigma T,
    G ⋆ Sigma ⊢# T <: T

(** [G ⋆ Sigma ⊢# S <: T]     #<br>#
    [G ⋆ Sigma ⊢# T <: U]     #<br>#
    [―――――――――――――]    #<br>#
    [G ⋆ Sigma ⊢# S <: U]         *)
| subtyp_trans_t: forall G Sigma S T U,
    G ⋆ Sigma ⊢# S <: T ->
    G ⋆ Sigma ⊢# T <: U ->
    G ⋆ Sigma ⊢# S <: U

(** [G ⋆ Sigma ⊢# T /\ U <: T] *)
| subtyp_and11_t: forall G Sigma T U,
    G ⋆ Sigma ⊢# typ_and T U <: T

(** [G ⋆ Sigma ⊢# T /\ U <: U] *)
| subtyp_and12_t: forall G Sigma T U,
    G ⋆ Sigma ⊢# typ_and T U <: U

(** [G ⋆ Sigma ⊢# S <: T]       #<br>#
    [G ⋆ Sigma ⊢# S <: U]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⋆ Sigma ⊢# S <: T /\ U]       *)
| subtyp_and2_t: forall G Sigma S T U,
    G ⋆ Sigma ⊢# S <: T ->
    G ⋆ Sigma ⊢# S <: U ->
    G ⋆ Sigma ⊢# S <: typ_and T U

(** [G ⋆ Sigma ⊢# T <: U]           #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# {a: T} <: {a: U}]     *)
| subtyp_fld_t: forall G Sigma a T U,
    G ⋆ Sigma ⊢# T <: U ->
    G ⋆ Sigma ⊢# typ_rcd (dec_trm a T) <: typ_rcd (dec_trm a U)

(** [G ⋆ Sigma ⊢# S2 <: S1]                   #<br>#
    [G ⋆ Sigma ⊢# T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ_t: forall G Sigma A S1 T1 S2 T2,
    G ⋆ Sigma ⊢# S2 <: S1 ->
    G ⋆ Sigma ⊢# T1 <: T2 ->
    G ⋆ Sigma ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⋆ Sigma ⊢! x: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# T <: x.A]         *)
| subtyp_sel2_t: forall G Sigma x A T,
    G ⋆ Sigma ⊢! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G ⋆ Sigma ⊢# T <: typ_sel (avar_f x) A

(** [G ⋆ Sigma ⊢! x: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢# x.A <: T]         *)
| subtyp_sel1_t: forall G Sigma x A T,
    G ⋆ Sigma ⊢! trm_var (avar_f x) : typ_rcd (dec_typ A T T) ->
    G ⋆ Sigma ⊢# typ_sel (avar_f x) A <: T

(** [G ⋆ Sigma ⊢# S2 <: S1]                #<br>#
    [G, x: S2 ⋆ Sigma ⊢ T1^x <: T2^x]       #<br>#
    [x fresh]                       #<br>#
    [――――――――――――――――――――――――]      #<br>#
    [G ⋆ Sigma ⊢# forall(S1)T1 <: forall(S2)T2]          *)
| subtyp_all_t: forall L G Sigma S1 T1 S2 T2,
    G ⋆ Sigma ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⋆ Sigma ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⋆ Sigma ⊢# typ_all S1 T1 <: typ_all S2 T2

(** [G ⋆ Sigma ⊢# T <: U ]            #<br>#
    [G ⋆ Sigma ⊢# U <: T ]            #<br>#
    [―――――――――――――――――――――――]     #<br>#
    [G ⋆ Sigma ⊢# Ref T <: Ref U]      *)
| subtyp_ref_t: forall G Sigma T U,
    G ⋆ Sigma ⊢# T <: U ->
    G ⋆ Sigma ⊢# U <: T ->
    G ⋆ Sigma ⊢# (typ_ref T) <: (typ_ref U)
where "G '⋆' Sigma '⊢#' T '<:' U" := (subtyp_t G Sigma T U).

Hint Constructors ty_trm_t subtyp_t.

Scheme ts_ty_trm_t_mut := Induction for ty_trm_t Sort Prop
with   ts_subtyp_t     := Induction for subtyp_t Sort Prop.
Combined Scheme ts_t_mutind from ts_ty_trm_t_mut, ts_subtyp_t.

(** Tight typing implies general typing. *)
Lemma tight_to_general:
  (forall G Sigma t T,
     G ⋆ Sigma ⊢# t : T ->
     G ⋆ Sigma ⊢ t : T) /\
  (forall G Sigma T U,
     G ⋆ Sigma ⊢# T <: U ->
     G ⋆ Sigma ⊢ T <: U).
Proof.
  apply ts_t_mutind; intros; subst; eauto using precise_to_general.
Qed.
