(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [|-##] and [ty_val_inv], [|-##v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import Sequences.
Require Import Definitions Binding.

(** * Lemmas about Replacement *)

Lemma repl_swap:
  (forall p q T T',
      repl_typ p q T T' ->
      repl_typ q p T' T) /\
  (forall p q D D',
      repl_dec p q D D' ->
      repl_dec q p D' D).
Proof.
  apply repl_mutind; intros; eauto.
Qed.

Lemma repl_open_rec:
  (forall p q T T',
      repl_typ p q T T' -> forall r n,
      named_path p ->
      named_path q ->
      repl_typ p q (open_rec_typ_p n r T) (open_rec_typ_p n r T')) /\
  (forall p q D D',
      repl_dec p q D D' -> forall r n,
      named_path p ->
      named_path q ->
      repl_dec p q (open_rec_dec_p n r D) (open_rec_dec_p n r D')).
Proof.
  apply repl_mutind; intros; try solve [unfolds open_typ_p, open_dec_p; simpls; eauto].
  - Case "rpath".
    subst. inversions H. destruct H1 as [bs' Heq]. inversions Heq.
    inversions H0. destruct H as [bs'' Heq]. inversions Heq. simpl. destruct r.
    apply* rpath.
  - Case "rsngl".
    subst. inversions H. destruct H1 as [bs' Heq]. inversions Heq.
    inversions H0. destruct H as [bs'' Heq]. inversions Heq. simpl. destruct r.
    apply* rsngl.
Qed.

Lemma repl_open: forall p q T T' r,
    repl_typ p q T T' ->
    named_path p ->
    named_path q ->
    repl_typ p q (open_typ_p r T) (open_typ_p r T').
Proof.
  unfold open_typ_p. intros. apply* repl_open_rec.
Qed.

Lemma repl_open_var: forall p q T T' x,
    repl_typ p q T T' ->
    named_path p ->
    named_path q ->
    repl_typ p q (open_typ x T) (open_typ x T').
Proof.
  introv Hr. repeat rewrite open_var_typ_eq. apply* repl_open.
Qed.

Definition repl_repeat_typ p q := star (repl_typ p q).
Definition repl_repeat_dec p q := star (repl_dec p q).

Lemma repl_star_rcd: forall p q d1 d2,
  repl_repeat_dec p q d1 d2 ->
  repl_repeat_typ p q (typ_rcd d1) (typ_rcd d2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_and1: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_and T1 U) (typ_and T2 U).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_and2: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_and U T1) (typ_and U T2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. apply star_trans with (b:=typ_and U b). apply star_one.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_bnd : forall T1 T2 p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_bnd T1) (typ_bnd T2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_all1: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_all T1 U) (typ_all T2 U).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_all2: forall T1 T2 U p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_typ p q (typ_all U T1) (typ_all U T2).
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. apply star_trans with (b:=typ_all U b). apply star_one.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_typ1: forall T1 T2 U A p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_dec p q {A >: T1 <: U} {A >: T2 <: U}.
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_typ2: forall T1 T2 U A p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_dec p q {A >: U <: T1} {A >: U <: T2}.
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. apply star_trans with (b:={A >: U <: b}). apply star_one.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_star_trm: forall T1 T2 a p q,
    repl_repeat_typ p q T1 T2 ->
    repl_repeat_dec p q {a ⦂ T1} {a ⦂ T2}.
Proof.
  introv Hs. dependent induction Hs.
  apply star_refl. eapply star_trans. apply star_one.
  destruct_all. repeat eexists. constructor*.
  eauto.
Qed.

Lemma repl_comp_open_rec:
  (forall T p q n,
      repl_repeat_typ p q (open_rec_typ_p n p T) (open_rec_typ_p n q T)) /\
  (forall D p q n,
      repl_repeat_dec p q (open_rec_dec_p n p D) (open_rec_dec_p n q D)).
Proof.
  apply typ_mutind; intros; unfolds repl_repeat_typ, repl_repeat_dec;
    simpl; try solve [apply star_refl]; eauto.
  - apply* repl_star_rcd. unfold repl_repeat_dec. eauto.
  - eapply star_trans.
    apply* repl_star_and1. apply* H.
    apply* repl_star_and2. apply* H0.
  - destruct p as [[pn | px] pbs]; destruct p0 as [p0x p0bs]; simpl.
    case_if; destruct q as [qx qbs]; subst. apply star_one. eauto.
    apply star_refl.
    destruct q as [qx qbs]. apply star_refl.
  - apply* repl_star_bnd. unfolds repl_repeat_typ. eauto.
  - eapply star_trans. apply repl_star_all1. apply* H. apply repl_star_all2. apply* H0.
  - destruct p as [[pn | px] pbs]; destruct p0 as [p0x p0bs]; simpl.
    case_if; destruct q as [qx qbs]; subst. apply star_one. eauto.
    apply star_refl.
    destruct q as [qx qbs]. apply star_refl.
  - eapply star_trans. apply repl_star_typ1. apply* H. apply repl_star_typ2. apply* H0.
  - apply* repl_star_trm. unfolds repl_repeat_typ. eauto.
Qed.

Lemma repl_comp_open: forall p q T,
    repl_repeat_typ p q (open_typ_p p T) (open_typ_p q T).
Proof.
  unfold open_typ_p. intros. apply* repl_comp_open_rec.
Qed.
