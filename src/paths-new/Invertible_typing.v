(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [|-##] and [ty_val_inv], [|-##v]). *)

Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Narrowing.
Require Import Helper_lemmas.
Require Import Precise_types.

(** Invertible-to-precise typing for field declarations: #<br>#
    [G |-## x: {a: T}]            #<br>#
    [――――――――――――――――――――――]      #<br>#
    [exists T', G |-! x: {a: T'}]      #<br>#
    [G |-# T' <: T]. *)
Lemma invertible_to_precise_trm_dec: forall G p a T,
  G ⊢## p : typ_rcd (dec_trm a T) ->
  exists T',
    G ⊢! trm_path p : typ_rcd (dec_trm a T') /\
    G ⊢# T' <: T.
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
    [G ⊢## x: forall(S)T]             #<br>#
    [――――――――――――――――――――――――――]  #<br>#
    [exists S', T'. G ⊢! x: forall(S')T']  #<br>#
    [G ⊢# S <: S']               #<br>#
    [G ⊢# T'^y <: T^y], where [y] is fresh. *)
Lemma invertible_to_precise_typ_all: forall G p S T,
  ok G ->
  G ⊢## p : typ_all S T ->
  exists S' T' L,
    G ⊢! trm_path p : typ_all S' T' /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - exists S T (dom G); auto.
  - specialize (IHHinv _ _ HG eq_refl).
    destruct IHHinv as [S' [T' [L' [Hpt [HSsub HTsub]]]]].
    exists S' T' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : G ⊢# typ_all S1 T1 <: typ_all S T).
    { apply subtyp_all_t with (L:=L); assumption. }
    split.
    + eapply subtyp_trans_t; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ S)) by auto using ok_push.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ S ⊢ open_typ y T' <: open_typ y T1).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

(** * Invertible Variable Typing *)

(** Invertible typing is closed under tight subtyping. *)
Lemma invertible_typing_closure_tight: forall G p T U,
  inert G ->
  G ⊢## p : T ->
  G ⊢# T <: U ->
  G ⊢## p : U.
Proof.
  intros G x T U Hgd HT Hsub.
  dependent induction Hsub; eauto.
  - inversion HT.
    destruct (precise_bot_false Hgd H).
  - inversion HT; auto. apply ty_and1_p in H. auto.
  - inversion HT; auto. apply ty_and2_p in H. auto.
  - inversions HT.
    + false* precise_psel_false.
    + pose proof (inert_unique_tight_bounds Hgd H H5) as Hu. subst. assumption.
Qed.

(** ** Tight-to-Invertible Lemma for Variables

       This lemma corresponds to Theorem 3.6 in the paper.

       [inert G]            #<br>#
       [G ⊢# x: U]         #<br>#
       [―――――――――――――――]    #<br>#
       [G ⊢## x: U] *)
Lemma tight_to_invertible :
  forall G U p,
    inert G ->
    G ⊢# trm_path p : U ->
    G ⊢## p : U.
Proof.
  intros G U x Hgd Hty.
  dependent induction Hty.
  - Case "ty_var_t".
    constructor. constructor*.
  - Case "ty_new_elim_t".
    specialize (IHHty _ Hgd eq_refl).
    dependent induction IHHty.
    * apply ty_fld_elim_p in H.
      constructor*.
    * apply invertible_typing_closure_tight with (T:=T0); auto.
      apply IHIHHty; auto. apply* inv_to_tight.
  - Case "ty_rec_intro_t".
    specialize (IHHty _ Hgd eq_refl).
    eapply ty_bnd_inv.
    apply IHHty.
  - Case "ty_rec_elim_t".
    specialize (IHHty _ Hgd eq_refl).
    inversion IHHty; subst; auto.
  - Case "ty_and_t".
    apply ty_and_inv; auto.
  - Case "ty_sub_t".
    eapply invertible_typing_closure_tight; auto.
Qed.

(** * Invertible Value Typing *)

(** Invertible value typing is closed under tight subtyping. *)
Lemma invertible_typing_closure_tight_v: forall G v T U,
  inert G ->
  G ⊢##v v : T ->
  G ⊢# T <: U ->
  G ⊢##v v : U.
Proof.
  introv Hgd HT Hsub.
  dependent induction Hsub; eauto; inversions HT; auto; try solve [inversion* H].
  - inversions H0.
  - lets Hb: (inert_unique_tight_bounds Hgd H H5). subst*.
Qed.

(** ** Tight-to-Invertible Lemma for Values

       [inert G]            #<br>#
       [G ⊢# v: T]         #<br>#
       [――――――――――――――――]   #<br>#
       [G ⊢##v v: T] *)
Lemma tight_to_invertible_v : forall G v T,
    inert G ->
    G ⊢# trm_val v : T ->
    G ⊢##v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl).
  apply* invertible_typing_closure_tight_v.
Qed.
