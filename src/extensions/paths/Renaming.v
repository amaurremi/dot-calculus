Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Some_lemmas.
Require Import Substitution.

Lemma ok_extend: forall E F x (v: typ),
  ok (E & F) ->
  x # (E & F) ->
  ok (E & x ~ v & F).
Proof.
  introv Hok Hn.
  induction F using env_ind; introv;
  autorewrite with rew_env_map; rew_env_concat.
  rewrite concat_empty_r in *. apply* ok_push.
  rewrite concat_assoc in *.
  apply ok_push; auto.
  intro. clear IHF. simpl_dom.
  rewrite in_union in H. destruct H. rewrite in_union in H. destruct H.
  - destruct (ok_push_inv Hok) as [_ Hnef].
    simpl_dom. rewrite notin_union in Hnef. destruct Hnef as [Hne _]. auto.
  - rewrite in_singleton in H. subst.
    rewrite notin_union in Hn. destruct Hn. apply notin_same in H. auto.
  - destruct (ok_push_inv Hok) as [_ Hnef].
    simpl_dom. rewrite notin_union in Hnef. destruct Hnef as [_ Hnf]. auto.
Qed.

Lemma fv_typ_ctx: forall x y T G,
  binds x T G ->
  y \in fv_typ T ->
  y \in fv_ctx_types G.
Proof.
  intros. induction G using env_ind.
  - false* binds_empty_inv.
  - destruct (binds_push_inv H) as [[Hx0 Hv] | [Hn Hb]];
    unfolds fv_ctx_types; unfolds fv_in_values;
    rewrite values_def, concat_def, single_def in *; simpl; subst; rewrite* in_union.
Qed.

Definition rename_var (x y z : var)  := If z = x then y else z.

Definition rename_ctx x y G := subst_ctx x y (map_keys (rename_var x y) G).

Lemma map_keys_notin: forall x y (G:ctx),
  x # G ->
  map_keys (rename_var x y) G = G.
Proof.
  intros. induction G using env_ind. rewrite map_keys_empty. reflexivity.
  rewrite map_keys_push. rewrite* IHG. assert (x <> x0) as Hxx0. {
    simpl_dom. rewrite notin_union in H. destruct H as [H _]. auto.
  }
  unfold rename_var. case_if. reflexivity.
Qed.

Lemma binds_map_keys: forall x y G' (T:typ) G'',
  ok (G' & x ~ T & G'') ->
  map_keys (rename_var x y) (G' & x ~ T & G'') = G' & y ~ T & G''.
Proof.
  intros. rewrite map_keys_concat. rewrite map_keys_push.
  destruct (ok_middle_inv H) as [H1 H2]. repeat rewrite* map_keys_notin.
  unfold rename_var. case_if. reflexivity.
Qed.

Lemma map_other_keys: forall x y z (G:ctx),
  z <> y ->
  z # G ->
  z # map_keys (rename_var x y) G.
Proof.
  intros. induction G using env_ind.
  rewrite map_keys_empty. assumption.
  rewrite map_keys_push. simpl_dom. rewrite notin_union. split.
  unfold rename_var. case_if*. auto.
Qed.

Lemma rename_ctx_other_var: forall x y z T (G: ctx),
    x <> z -> rename_ctx x y G & z ~ subst_typ x y T = rename_ctx x y (G & z ~ T).
Proof.
  intros. unfold rename_ctx. unfold subst_ctx. rewrite map_keys_concat.
  replace (map_keys (rename_var x y) (z ~ T)) with (z ~ T).
  - rewrite map_push. reflexivity.
  - rewrite* map_keys_notin.
Qed.

Lemma renaming_gen: forall x y,
  (forall G t T, G |- t: T ->
    ok G ->
    y # G ->
    rename_ctx x y G |- subst_trm x y t: subst_typ x y T) /\
  (forall G p T, G |-\||/ p: T ->
    ok G ->
    y # G ->
    rename_ctx x y G |-\||/ subst_path x y p: subst_typ x y T) /\
  (forall G z U d D, G && z ~ U |- d: D ->
    ok (G & z ~ U) ->
    y # (G & z ~ U) ->
    rename_ctx x y G && rename_var x y z ~ subst_typ x y U |-
          subst_def x y d : subst_dec x y D) /\
  (forall G z U ds T, G && z ~ U |- ds :: T ->
    ok (G & z ~ U) ->
    y # (G & z ~ U) ->
    rename_ctx x y G && rename_var x y z ~ subst_typ x y U |- subst_defs x y ds :: subst_typ x y T) /\
  (forall G T U, G |- T <: U ->
    ok G ->
    y # G ->
    rename_ctx x y G |- subst_typ x y T <: subst_typ x y U).
Proof.
  intros. apply rules_mutind; intros; subst; simpl; try (econstructor; apply* H); eauto.
  - (* ty_var *)
    constructor. unfold rename_ctx. unfold subst_ctx.
    destruct (binds_destruct b) as [G' [G'' HG]]. case_if. subst. rewrite* binds_map_keys.
    apply binds_map. subst. rewrite map_keys_concat. rewrite map_keys_push.
    destruct (ok_middle_inv H) as [Hl Hr].
    assert (x0 <> y) as Hx0y. {
      simpl_dom. repeat rewrite notin_union in H1. auto.
    }
    lets Ho: (map_other_keys Hx0y Hr (x:=x)). unfold rename_var. case_if. apply binds_middle_eq. auto.
  - (* ty_all_intro *)
    apply_fresh ty_all_intro as z. assert (z \notin L) as Lz by auto. specialize (H z Lz).
    rewrite subst_open_commute_trm in H. rewrite subst_open_commute_typ in H.
    unfold subst_fvar in H. assert (z <> x) as Hzx by auto. case_if.
    rewrite* rename_ctx_other_var.
  - (* ty_all_elim *)
    rewrite subst_open_commute_typ. apply ty_all_elim with (S:=(subst_typ x y S)); auto.
  - (* ty_new_intro *)
    apply_fresh ty_new_intro as z. assert (Lz: z \notin L) by auto. specialize (H z Lz).
    rewrite subst_open_commute_typ in H. rewrite subst_open_commute_defs in H.
    unfold rename_var in H. unfold subst_fvar in H. assert (Hzx: z <> x) by auto.
    case_if. apply* H.
  - (* ty_let *)
    apply_fresh ty_let as z; auto. assert (Lz: z \notin L) by auto. specialize (H0 z Lz).
    rewrite subst_open_commute_trm in H0.
    unfold subst_fvar in H0. assert (Hzx: z <> x) by auto. case_if.
    rewrite* rename_ctx_other_var.
  - (* ty_rec_intro *)
    apply ty_rec_intro. simpl in H. rewrite subst_open_commute_typ in H. unfold subst_fvar in H. apply* H.
  - (* ty_rec_elim. *)
    rewrite subst_open_commute_typ. apply ty_rec_elim. unfold subst_typ in H.
    apply* H.
  - simpls. rewrite subst_open_commute_typ_p. apply* ty_p_rec_elim.
  - simpls. apply* ty_p_fld_elim. apply* inert_sngl_subst.
  - (* ty_def_trm *)
    apply ty_def_trm.
    replace (rename_ctx x y G & rename_var x y z ~ subst_typ x y U) with (rename_ctx x y (G & z ~ U)).
    + apply* H.
    + unfold rename_ctx. rewrite map_keys_concat. rewrite map_keys_single.
      unfold subst_ctx. apply map_push.
  - (* ty_def val *)
    apply ty_def_val.
     replace (rename_ctx x y G & rename_var x y z ~ subst_typ x y U) with (rename_ctx x y (G & z ~ U)).
    + apply* H.
    + unfold rename_ctx. rewrite map_keys_concat. rewrite map_keys_single.
      unfold subst_ctx. apply map_push.
  - (* ty_defs_cons *)
    apply* ty_defs_cons. apply subst_defs_hasnt. rewrite <- subst_label_of_def. assumption.
  - (* subtyp_sngl_sel1 *)
    specialize (H0 H1 H2). simpls. apply* subtyp_sngl_sel1.
  - (* subtyp_sngl_sel2 *)
    specialize (H0 H1 H2). simpls. apply* subtyp_sngl_sel2.
  - (* subtyp_all *)
    apply_fresh subtyp_all as z; auto. specialize (H0 z). assert (Hzx: z <> x) by auto.
    rewrite rename_ctx_other_var; auto. repeat rewrite subst_open_commute_typ in H0.
    unfold subst_fvar in H0. case_if. apply* H0.
Qed.

Lemma renaming_def: forall G z U ds T y,
  ty_defs G z U ds T ->
  ok (G & z ~ U) ->
  y # (G & z ~ U) ->
  z \notin fv_ctx_types G ->
  ty_defs G y (subst_typ z y U) (subst_defs z y ds) (subst_typ z y T).
Proof.
  introv Hds Hok Hy Hz.
  assert (HG: G = subst_ctx z y G) by (rewrite (subst_fresh_ctx y G Hz); reflexivity).
  destruct (ok_push_inv Hok) as [_ Hn].
  assert (HG': G = (map_keys (rename_var z y) G)) by rewrite* map_keys_notin.
  assert (Hrg: G = rename_ctx z y G). {
    unfold rename_ctx. rewrite <- HG'. assumption.
  }
  lets Hr: (proj54 (renaming_gen z y)).
  specialize (Hr G z U ds T Hds Hok Hy).
  rewrite Hrg.
  assert (Hyz: y = (rename_var z y z)). {
    unfold rename_var. case_if. reflexivity.
  }
  rewrite <- Hyz in Hr. assumption.
Qed.
