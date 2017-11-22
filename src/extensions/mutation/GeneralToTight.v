(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import RecordAndInertTypes.
Require Import PreciseTyping.
Require Import TightTyping.
Require Import InvertibleTyping.

(** * Sel-<: Premise
    This lemma corresponds to Lemma 3.5 in the paper.

    [inert G]                    #<br>#
    [G ⋆ Sigma ⊢## x: {A: S..U}]        #<br>#
    [――――――――――――――――――――――――――――]   #<br>#
    [exists T. G ⋆ Sigma ⊢## x: {A: T..T}]   #<br>#
    [G ⋆ Sigma ⊢# T <: U]               #<br>#
    [G ⋆ Sigma ⊢# S <: T]                    *)
Lemma sel_premise: forall G Sigma x A U V,
  inert G ->
  G ⋆ Sigma ⊢## x : typ_rcd (dec_typ A U V) ->
  exists T,
    G ⋆ Sigma ⊢! trm_var (avar_f x) : typ_rcd (dec_typ A T T) /\
    G ⋆ Sigma ⊢# T <: V /\
    G ⋆ Sigma ⊢# U <: T.
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - lets Hp: (precise_dec_typ_inv HG H). subst.
    exists; split*.
  - specialize (IHHinv A T U0 HG eq_refl).
    destruct IHHinv as [? [Hx [Hs1 Hs2]]].
    exists; split*.
Qed.

(** * Sel-<: Replacement
    This lemma corresponds to Lemma 3.4 in the paper.

    [inert G]              #<br>#
    [G ⋆ Sigma ⊢# x: {A: S..U}]   #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⋆ Sigma ⊢# x.A <: U]       #<br>#
    [G ⋆ Sigma ⊢# S <: x.A]            *)
Lemma sel_replacement: forall G Sigma x A T U,
    inert G ->
    G ⋆ Sigma ⊢# trm_var (avar_f x) : typ_rcd (dec_typ A T U) ->
    (G ⋆ Sigma ⊢# typ_sel (avar_f x) A <: U /\
     G ⋆ Sigma ⊢# T <: typ_sel (avar_f x) A).
Proof.
  introv HG Hty.
  pose proof (tight_to_invertible HG Hty) as Hinv.
  pose proof (sel_premise HG Hinv) as [? [Ht [Hs1 Hs2]]].
  split; eauto using subtyp_trans_t, subtyp_sel1_t, subtyp_sel2_t.
Qed.

(** * General to Tight [⊢ to ⋆ Sigma ⊢#] *)
(** The following lemma corresponds to Theorem 3.3 in the paper.
    It says that in an inert environment, general typing ([ty_trm] [⊢]) can
    be reduced to tight typing ([ty_trm_t] [⊢#]).
    The proof is by mutual induction on the typing and subtyping judgements.

    [inert G]           #<br>#
    [G ⋆ Sigma ⊢ t: T]          #<br>#
    [――――――――――――――]    #<br>#
    [G ⋆ Sigma ⊢# t: T] #<br># #<br>#

    and                 #<br># #<br>#
    [inert G]           #<br>#
    [G ⋆ Sigma ⊢ S <: U]        #<br>#
    [――――――――――――――――]  #<br>#
    [G ⋆ Sigma ⊢# S <: U]         *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G Sigma t T,
     G ⋆ Sigma ⊢ t : T ->
     G = G0 ->
     G ⋆ Sigma ⊢# t : T) /\
  (forall G Sigma T U,
     G ⋆ Sigma ⊢ T <: U ->
     G = G0 ->
     G ⋆ Sigma ⊢# T <: U).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst; try solve [eapply sel_replacement; auto]; eauto.
Qed.

(** The general-to-tight lemma, formulated for term typing. *)
Lemma general_to_tight_typing: forall G Sigma t T,
  inert G ->
  G ⋆ Sigma ⊢ t : T ->
  G ⋆ Sigma ⊢# t : T.
Proof.
  intros. apply* general_to_tight.
Qed.
