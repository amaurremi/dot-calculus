(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [⊢##] and [ty_val_inv], [⊢##v]). *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import RecordAndInertTypes.
Require Import Subenvironments.
Require Import Narrowing.
Require Import PreciseTyping.
Require Import TightTyping.

(** The invertible-typing relation describes the possible types that a variable or value
can be typed with in an inert context. For example, if [G] is inert, [G ⋆ Sigma ⊢! x: {a: T}],
and [G ⋆ Sigma ⊢ T <: T'], then [G ⋆ Sigma ⊢## x: {a: T'}].

The purpose of invertible typing is to be easily invertible into a precise typing relation.
To achieve that, invertible typing avoids typing cycles that could result from, for example,
repeated applications of recursion introduction and elimination.
For this case, invertible typing defines only recursion introduction (whereas precise typing
defines only recursion elimination). *)

(** * Invertible typing of variables [G ⋆ Sigma ⊢## x: T] *)

Reserved Notation "G ⋆ Sigma '⊢##' x ':' T" (at level 40, x at level 59).

Inductive ty_var_inv : ctx -> stoty -> var -> typ -> Prop :=

(** [G ⋆ Sigma ⊢! x: T]  #<br>#
    [―――――――――――] #<br>#
    [G ⋆ Sigma ⊢## x: T]     *)
| ty_precise_inv : forall G Sigma x T,
  G ⋆ Sigma ⊢! trm_var (avar_f x) : T ->
  G ⋆ Sigma ⊢## x : T

(** [G ⋆ Sigma ⊢## x: {a: T}] #<br>#
    [G ⋆ Sigma ⊢# T <: U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢## x: {a: U}]     *)
| ty_dec_trm_inv : forall G Sigma x a T U,
  G ⋆ Sigma ⊢## x : typ_rcd (dec_trm a T) ->
  G ⋆ Sigma ⊢# T <: U ->
  G ⋆ Sigma ⊢## x : typ_rcd (dec_trm a U)

(** [G ⋆ Sigma ⊢## x: {A: T..U}]   #<br>#
    [G ⋆ Sigma ⊢# T' <: T]         #<br>#
    [G ⋆ Sigma ⊢# U <: U']         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢## x: {A: T'..U'}]     *)
| ty_dec_typ_inv : forall G Sigma x A T T' U' U,
  G ⋆ Sigma ⊢## x : typ_rcd (dec_typ A T U) ->
  G ⋆ Sigma ⊢# T' <: T ->
  G ⋆ Sigma ⊢# U <: U' ->
  G ⋆ Sigma ⊢## x : typ_rcd (dec_typ A T' U')

(** [G ⋆ Sigma ⊢## x: T^x]   #<br>#
    [―――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢## x: mu(T)] *)
| ty_bnd_inv : forall G Sigma x T,
  G ⋆ Sigma ⊢## x : open_typ x T ->
  G ⋆ Sigma ⊢## x : typ_bnd T

(** [G ⋆ Sigma ⊢## x: forall(S)T]          #<br>#
    [G ⋆ Sigma ⊢# S' <: S]            #<br>#
    [G, y: S' ⋆ Sigma ⊢ T^y <: T'^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⋆ Sigma ⊢## x: forall(S')T']            *)
| ty_all_inv : forall L G Sigma x S1 T S2 T',
  G ⋆ Sigma ⊢## x : typ_all S1 T ->
  G ⋆ Sigma ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⋆ Sigma ⊢ open_typ y T <: open_typ y T') ->
  G ⋆ Sigma ⊢## x : typ_all S2 T'

(** [G ⋆ Sigma ⊢## x : T]     #<br>#
    [G ⋆ Sigma ⊢## x : U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢## x : T /\ U]      *)
| ty_and_inv : forall G Sigma x S1 S2,
  G ⋆ Sigma ⊢## x : S1 ->
  G ⋆ Sigma ⊢## x : S2 ->
  G ⋆ Sigma ⊢## x : typ_and S1 S2

(** [G ⋆ Sigma ⊢## x: S]        #<br>#
    [G ⋆ Sigma ⊢! y: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢## x: y.A           *)
| ty_sel_inv : forall G Sigma x y A T,
  G ⋆ Sigma ⊢## x : T ->
  G ⋆ Sigma ⊢! trm_var y : typ_rcd (dec_typ A T T) ->
  G ⋆ Sigma ⊢## x : typ_sel y A

(** [G ⋆ Sigma ⊢## x : Ref T] #<br>#
    [G ⋆ Sigma ⊢## T <: U]    #<br>#
    [G ⋆ Sigma ⊢## U <: T]    #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢## x : Ref T]     *)
| ty_loc_inv : forall G Sigma x T U,
  G ⋆ Sigma ⊢## x : typ_ref T ->
  G ⋆ Sigma ⊢# T <: U ->
  G ⋆ Sigma ⊢# U <: T ->
  G ⋆ Sigma ⊢## x : typ_ref U

(** [G ⋆ Sigma ⊢## x: T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⋆ Sigma ⊢## x: top]     *)
| ty_top_inv : forall G Sigma x T,
  G ⋆ Sigma ⊢## x : T ->
  G ⋆ Sigma ⊢## x : typ_top
where "G ⋆ Sigma '⊢##' x ':' T" := (ty_var_inv G Sigma x T).

(** *** Invertible typing of values [G ⋆ Sigma ⊢##v v: T] *)

Reserved Notation "G ⋆ Sigma '⊢##v' v ':' T" (at level 40, v at level 59).

Inductive ty_val_inv : ctx -> stoty -> val -> typ -> Prop :=

(** [G ⋆ Sigma ⊢! v: T]    #<br>#
    [―――――――――――――] #<br>#
    [G ⋆ Sigma ⊢##v v: T] *)
| ty_precise_inv_v : forall G Sigma v T,
  G ⋆ Sigma ⊢! trm_val v : T ->
  G ⋆ Sigma ⊢##v v : T

(** [G ⋆ Sigma ⊢##v v: forall(S)T]          #<br>#
    [G ⋆ Sigma ⊢# S' <: S]             #<br>#
    [G, y: S' ⋆ Sigma ⊢ T^y <: T'^y]    #<br>#
    [y fresh]                   #<br>#
    [――――――――――――――――――――――]    #<br>#
    [G ⋆ Sigma ⊢##v v: forall(S')T']            *)
| ty_all_inv_v : forall L G Sigma v S1 T S2 T',
  G ⋆ Sigma ⊢##v v : typ_all S1 T ->
  G ⋆ Sigma ⊢# S2 <: S1 ->
  (forall y, y \notin L ->
   G & y ~ S2 ⋆ Sigma ⊢ open_typ y T <: open_typ y T') ->
  G ⋆ Sigma ⊢##v v : typ_all S2 T'

(** [G ⋆ Sigma ⊢##v v: S]       #<br>#
    [G ⋆ Sigma ⊢! y: {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢##v v: y.A]         *)
| ty_sel_inv_v : forall G Sigma v y A T,
  G ⋆ Sigma ⊢##v v : T ->
  G ⋆ Sigma ⊢! trm_var y : typ_rcd (dec_typ A T T) ->
  G ⋆ Sigma ⊢##v v : typ_sel y A

(** [G ⋆ Sigma ⊢##v v : T]        #<br>#
    [G ⋆ Sigma ⊢##v v : U]        #<br>#
    [―――――――――――――]        #<br>#
    [G ⋆ Sigma ⊢##v v : T /\ U]        *)
| ty_and_inv_v : forall G Sigma v T U,
  G ⋆ Sigma ⊢##v v : T ->
  G ⋆ Sigma ⊢##v v : U ->
  G ⋆ Sigma ⊢##v v : typ_and T U

(** [G ⋆ Sigma ⊢##v v : Ref T] #<br>#
    [G ⋆ Sigma ⊢##v T <: U]    #<br>#
    [G ⋆ Sigma ⊢##v U <: T]    #<br>#
    [――――――――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢##v v : Ref T]     *)
| ty_loc_inv_v : forall G Sigma v T U,
  G ⋆ Sigma ⊢##v v : typ_ref T ->
  G ⋆ Sigma ⊢# T <: U ->
  G ⋆ Sigma ⊢# U <: T ->
  G ⋆ Sigma ⊢##v v : typ_ref U

(** [G ⋆ Sigma ⊢##v v: T]   #<br>#
    [――――――――――――――] #<br>#
    [G ⋆ Sigma ⊢##v v: top]     *)
| ty_top_inv_v : forall G Sigma v T,
  G ⋆ Sigma ⊢##v v : T ->
  G ⋆ Sigma ⊢##v v : typ_top
where "G ⋆ Sigma '⊢##v' v ':' T" := (ty_val_inv G Sigma v T).

Hint Constructors ty_var_inv ty_val_inv.

(** ** Invertible to Precise Typing [|-## to |-!] *)

(** Invertible-to-precise typing for field declarations: #<br>#
    [G ⋆ Sigma ⊢## x: {a: T}]            #<br>#
    [――――――――――――――――――――――]      #<br>#
    [exists T', G ⋆ Sigma ⊢! x: {a: T'}]      #<br>#
    [G ⋆ Sigma ⊢# T' <: T]. *)
Lemma invertible_to_precise_trm_dec: forall G Sigma x a T,
  G ⋆ Sigma ⊢## x : typ_rcd (dec_trm a T) ->
  exists T',
    G ⋆ Sigma ⊢! trm_var (avar_f x) : typ_rcd (dec_trm a T') /\
    G ⋆ Sigma ⊢# T' <: T.
Proof.
  introv Hinv.
  dependent induction Hinv.
  - exists T. auto.
  - specialize (IHHinv _ _ eq_refl). destruct IHHinv as [V [Hx Hs]].
    exists V. split; auto.
    eapply subtyp_trans_t; eassumption.
Qed.

(** Invertible-to-precise typing for function types: #<br>#
    [ok G]                        #<br>#
    [G ⋆ Sigma ⊢## x: forall(S)T]             #<br>#
    [――――――――――――――――――――――――――]  #<br>#
    [exists S', T'. G ⋆ Sigma ⊢! x: forall(S')T']  #<br>#
    [G ⋆ Sigma ⊢# S <: S']               #<br>#
    [G ⋆ Sigma ⊢# T'^y <: T^y], where [y] is fresh. *)
Lemma invertible_to_precise_typ_all: forall G Sigma x T U,
  ok G ->
  G ⋆ Sigma ⊢## x : typ_all T U ->
  exists T' U' L,
    G ⋆ Sigma ⊢! trm_var (avar_f x) : typ_all T' U' /\
    G ⋆ Sigma ⊢# T <: T' /\
    (forall y,
        y \notin L ->
            G & y ~ T ⋆ Sigma ⊢ open_typ y U' <: open_typ y U).
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - exists T U (dom G); auto.
  - specialize (IHHinv _ _ HG eq_refl).
    destruct IHHinv as [T' [U' [L' [Hpt [HSsub HTsub]]]]].
    exists T' U' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : G ⋆ Sigma ⊢# typ_all S1 T0 <: typ_all T U).
    { apply subtyp_all_t with (L:=L); assumption. }
    split.
    + eapply subtyp_trans_t; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ T)) by auto using ok_push.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ T ⋆ Sigma ⊢ open_typ y U' <: open_typ y T0).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

Lemma invertible_to_precise_typ_ref: forall G Sigma x T,
  ok G ->
  G ⋆ Sigma ⊢## x : typ_ref T ->
  exists T',
    G ⋆ Sigma ⊢! trm_var (avar_f x) : typ_ref T' /\
    G ⋆ Sigma ⊢# T <: T' /\
    G ⋆ Sigma ⊢# T' <: T.
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - exists T; auto.
  - destruct (IHHinv _ HG eq_refl) as [?T [? [? ?]]].
    exists T1; auto. split*.
Qed.

(** ** Invertible Subtyping Closure *)

(** Invertible typing is closed under tight subtyping. *)
Lemma invertible_typing_closure_tight: forall G Sigma x T U,
  inert G ->
  G ⋆ Sigma ⊢## x : T ->
  G ⋆ Sigma ⊢# T <: U ->
  G ⋆ Sigma ⊢## x : U.
Proof.
  intros G S x T U Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversion HT.
    destruct (precise_bot_false Hgd H).
  - inversion HT; auto. apply ty_and1_p in H. auto.
  - inversion HT; auto. apply ty_and2_p in H. auto.
  - inversions HT.
    + false* precise_psel_false.
    + pose proof (inert_unique_tight_bounds Hgd H H6) as Hu. subst. assumption.
Qed.

(** ** Tight-to-Invertible Lemma for Variables [|-# to |-##]

       This lemma corresponds to Theorem 3.6 in the paper.

       [inert G]            #<br>#
       [G ⋆ Sigma ⊢# x: U]         #<br>#
       [―――――――――――――――]    #<br>#
       [G ⋆ Sigma ⊢## x: U] *)
Lemma tight_to_invertible :
  forall G Sigma U x,
    inert G ->
    G ⋆ Sigma ⊢# trm_var (avar_f x) : U ->
    G ⋆ Sigma ⊢## x : U.
Proof.
  introv Hgd Hty.
  dependent induction Hty.
  - auto.
  - specialize (IHHty _ Hgd eq_refl).
    eapply ty_bnd_inv.
    apply IHHty.
  - specialize (IHHty _ Hgd eq_refl).
    inversion IHHty; subst; auto.
  - apply ty_and_inv; auto.
  - eapply invertible_typing_closure_tight; auto.
Qed.

(** * Invertible Value Typing *)

(** ** Invertible Subtyping Closure *)

(** Invertible value typing is closed under tight subtyping. *)
Lemma invertible_typing_closure_tight_v: forall G Sigma v T U,
  inert G ->
  G ⋆ Sigma ⊢##v v : T ->
  G ⋆ Sigma ⊢# T <: U ->
  G ⋆ Sigma ⊢##v v : U.
Proof.
  introv Hgd HT Hsub.
  dependent induction Hsub; eauto; inversions HT; auto; try solve [inversion* H].
  - inversions H0.
  - lets Hb: (inert_unique_tight_bounds Hgd H H6). subst*.
Qed.

(** ** Tight-to-Invertible Lemma for Values [|-# to |-##]

       [inert G]            #<br>#
       [G ⋆ Sigma ⊢# v: T]         #<br>#
       [――――――――――――――――]   #<br>#
       [G ⋆ Sigma ⊢##v v: T] *)
Lemma tight_to_invertible_v : forall G Sigma v T,
    inert G ->
    G ⋆ Sigma ⊢# trm_val v : T ->
    G ⋆ Sigma ⊢##v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl).
  eapply invertible_typing_closure_tight_v; eauto.
Qed.
