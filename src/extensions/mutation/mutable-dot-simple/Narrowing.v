Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.

(* ###################################################################### *)
(** ** Narrowing *)

Definition subenv(G1 G2: ctx) (S: sigma) :=
  forall x T2, binds x T2 G2 ->
    binds x T2 G1 \/
    exists T1,
      binds x T1 G1 /\ subtyp sub_general G1 S T1 T2.

Lemma subenv_push: forall G G' S x T,
  subenv G' G S ->
  ok (G' & x ~ T) ->
  subenv (G' & x ~ T) (G & x ~ T) S.
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
      exists T'. split. eauto. apply weaken_subtyp_ctx. assumption. eauto.
Qed.

Lemma subenv_last: forall G S x V U,
  subtyp sub_general G S V U ->
  ok (G & x ~ V) ->
  subenv (G & x ~ V) (G & x ~ U) S.
Proof.
  intros. unfold subenv. intros y T Bi.
  apply binds_push_inv in Bi. destruct Bi as [Bi | Bi].
  - destruct Bi. subst. right. exists V. split; eauto using weaken_subtyp_ctx.
  - destruct Bi. left. eauto.
Qed.

Lemma narrow_rules:
  (forall m1 m2 G S t T, ty_trm m1 m2 G S t T -> forall G',
    m1 = ty_general ->
    m2 = sub_general ->
    ok G' ->
    subenv G' G S ->
    ty_trm m1 m2 G' S t T)
/\ (forall G S d D, ty_def G S d D -> forall G',
    ok G' ->
    subenv G' G S ->
    ty_def G' S d D)
/\ (forall G S ds T, ty_defs G S ds T -> forall G',
    ok G' ->
    subenv G' G S ->
    ty_defs G' S ds T)
/\ (forall m2 G S V U, subtyp m2 G S V U -> forall G',
    m2 = sub_general ->
    ok G' ->
    subenv G' G S ->
    subtyp m2 G' S V U).
Proof.
  apply rules_mutind; intros; eauto 4.
  - (* ty_var *)
    subst. unfold subenv in H2. specialize (H2 x T b).
    destruct H2.
    + eauto.
    + destruct H as [T' [Bi Hsub]].
      eapply ty_sub; eauto.
  - (* ty_all_intro *)
    subst.
    apply_fresh ty_all_intro as y; eauto using subenv_push.
  - (* ty_new_intro *)
    subst.
    apply_fresh ty_new_intro as y; eauto using subenv_push.
  - (* ty_let *)
    subst.
    apply_fresh ty_let as y; eauto using subenv_push.
  - inversion H0 (* sub_tight *).
  - inversion H0 (* sub_tight *).
  - (* subtyp_all *)
    subst.
    apply_fresh subtyp_all as y.
    + eauto.
    + assert (H5: ok (G' & y ~ S2)) by auto.
      eauto using subenv_push.
Qed.

Lemma narrow_typing: forall G G' S t T,
  ty_trm ty_general sub_general G S t T ->
  subenv G' G S -> ok G' ->
  ty_trm ty_general sub_general G' S t T.
Proof.
  intros. apply* narrow_rules.
Qed.

Lemma narrow_subtyping: forall G G' S V U,
  subtyp sub_general G S V U ->
  subenv G' G S -> ok G' ->
  subtyp sub_general G' S V U.
Proof.
  intros. apply* narrow_rules.
Qed.
