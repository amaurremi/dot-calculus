Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.

(* ###################################################################### *)
(** ** Narrowing *)

Definition subenv(G1 G2: ctx) :=
  forall x T2, binds x T2 G2 ->
    binds x T2 G1 \/
    exists T1,
      binds x T1 G1 /\ G1 |- T1 <: T2.

Lemma subenv_push: forall G G' x T,
  subenv G' G ->
  ok (G' & x ~ T) ->
  subenv (G' & x ~ T) (G & x ~ T).
Proof.
  intros.
  unfold subenv. intros xb Tb Bi. apply binds_push_inv in Bi.
  destruct Bi as [Bi | Bi].
  + destruct Bi as [Bi1 Bi2]. subst.
    left. eauto.
  + destruct Bi as [Bi1 Bi2].
    unfold subenv in H. specialize (H xb Tb Bi2). destruct H as [Bi' | Bi'].
    * left. eauto.
    * right. destruct Bi' as [T' [Bi1' Bi2']].
      exists T'. split. eauto. apply weaken_subtyp. assumption. eauto.
Qed.

Lemma subenv_last: forall G x S U,
  G |- S <: U ->
  ok (G & x ~ S) ->
  subenv (G & x ~ S) (G & x ~ U).
Proof.
  intros. unfold subenv. intros y T Bi.
  apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
  - destruct Bi. subst. right. exists S. split; eauto using weaken_subtyp.
  - destruct Bi. left. eauto.
Qed.

Lemma narrow_rules:
  (forall G t T, G |- t : T -> forall G',
    ok G' ->
    subenv G' G ->
    G' |- t : T)
/\ (forall G p T, G |-\||/ p: T -> forall G',
    ok G' ->
    subenv G' G ->
    G' |-\||/ p : T)
/\ (forall G z U d D, G && z ~ U |- d : D -> forall G',
    ok (G' & z ~ U) ->
    subenv G' G ->
    G' && z ~ U |- d : D)
/\ (forall G z U ds T, G && z ~ U |- ds :: T -> forall G',
    ok (G' & z ~ U) ->
    subenv G' G ->
    G' && z ~ U |- ds :: T)
/\ (forall G S U, G |- S <: U -> forall G',
    ok G' ->
    subenv G' G ->
    G' |- S <: U).
Proof.
  apply rules_mutind; intros; eauto 4.
  - (* ty_var *)
    subst. unfold subenv in H0. specialize (H0 x T b).
    destruct* H0. destruct H0 as [T' [Bi Hsub]]. eapply ty_sub; eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto using subenv_push.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as z. apply H; auto.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto using subenv_push.
 - (* ty_def_path *)
    constructor. apply H; auto. apply subenv_push. assumption. assumption.
  - (* ty_def_val *)
    constructor. apply H; auto. apply subenv_push. assumption. assumption.
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y; eauto.
    apply H0; eauto. apply subenv_push; eauto.
Qed.

Lemma narrow_typing: forall G G' t T,
  G |- t : T ->
  subenv G' G ->
  ok G' ->
  G' |- t : T.
Proof.
  intros. apply* narrow_rules.
Qed.

Lemma narrow_subtyping: forall G G' S U,
  G |- S <: U ->
  subenv G' G ->
  ok G' ->
  G' |- S <: U.
Proof.
  intros. apply* narrow_rules.
Qed.
