Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Weakening.
Require Import Wellformed_store.
Require Import Substitution.
Require Import Some_lemmas.
Require Import Inert_types.
Require Import General_to_tight.
Require Import Renaming.
Require Import Invertible_typing.

Lemma defs_has_hasnt_neq: forall ds d1 d2,
  defs_has ds d1 ->
  defs_hasnt ds (label_of_def d2) ->
  label_of_def d1 <> label_of_def d2.
Proof.
  introv Hhas Hhasnt.
  unfold defs_has in Hhas.
  unfold defs_hasnt in Hhasnt.
  induction ds.
  - simpl in Hhas. inversion Hhas.
  - simpl in Hhasnt. simpl in Hhas. case_if; case_if.
    + inversions Hhas. assumption.
    + apply IHds; eauto.
Qed.

Lemma record_has_ty_defs: forall G z U T ds D,
  G && z ~ U |- ds :: T ->
  record_has T D ->
  exists d, defs_has ds d /\ G && z ~ U |- d : D.
Proof.
  introv Hdefs Hhas. induction Hdefs.
  - inversion Hhas; subst. exists d. split.
    + unfold defs_has. simpl. rewrite If_l; reflexivity.
    + assumption.
  - inversion Hhas; subst.
    + destruct (IHHdefs H4) as [d' [H1 H2]].
      exists d'. split.
      * unfold defs_has. simpl. rewrite If_r. apply H1.
        apply not_eq_sym. eapply defs_has_hasnt_neq; eauto.
      * assumption.
    + exists d. split.
      * unfold defs_has. simpl. rewrite If_l; reflexivity.
      * inversions* H4.
Qed.

Lemma inert_sub: forall G G',
    inert (G & G') -> inert G.
Proof.
  introv. gen G. induction G' using env_ind; introv Hi.
  rewrite concat_empty_r in Hi. assumption. rewrite concat_assoc in Hi.
  inversions Hi. false* empty_push_inv.
  apply eq_push_inv in H. destruct H as [Hx [HT HG]]. subst. apply* IHG'.
Qed.

Lemma wf_sto_sub: forall G G' G'' s s' s'' x T v,
  wf_sto G s ->
  G = G' & x ~ T & G'' ->
  s = s' & x ~ v & s'' ->
  wf_sto (G' & x ~ T) (s' & x ~ v).
Proof.
  introv Hwf HG Hs. gen G G' s s' s''.
  induction G'' using env_ind; intros G G' HG s Hwf s' s'' Hs; destruct s'' using env_ind.
  - rewrite concat_empty_r in *. subst. assumption.
  - rewrite concat_assoc in Hs. subst. rewrite concat_empty_r in Hwf.
    assert (x <> x0) as Hxn. {
      lets Hok: (wf_sto_to_ok_s Hwf). destruct (ok_push_inv Hok) as [_ Hn].
      simpl_dom. auto.
    }
    inversion Hwf. false* empty_push_inv.
    destruct (eq_push_inv H0) as [Hx _]. destruct (eq_push_inv H) as [Hx' _]. subst. subst.
    false* Hxn.
  - rewrite concat_assoc in HG. subst. rewrite concat_empty_r in Hwf.
    assert (x <> x0) as Hxn. {
      lets Hok: (wf_sto_to_ok_G Hwf). destruct (ok_push_inv Hok) as [_ Hn].
      simpl_dom. auto.
    }
    inversion Hwf. false* empty_push_inv.
    destruct (eq_push_inv H0) as [Hx _]. destruct (eq_push_inv H) as [Hx' _]. subst. subst.
    false* Hxn.
  - assert (G' & x ~ T & G'' = G' & x ~ T & G'') as Hobv by reflexivity.
    assert (wf_sto (G' & x ~ T & G'') (s' & x ~ v & s'')) as Hwf'. {
      subst. inversion Hwf.
      * false* empty_middle_inv.
      * rewrite concat_assoc in *.
        destruct (eq_push_inv H) as [Hx [Ht Hg]]. destruct (eq_push_inv H0) as [Hx' [Hv Hs']].
        subst. subst. assumption.
    }
    assert (s' & x ~ v & s'' = s' & x ~ v & s'') as Hobv' by reflexivity.
    specialize (IHG'' (G' & x ~ T & G'') G' Hobv (s' & x ~ v & s'') Hwf' s' s'' Hobv').
    apply IHG''.
Qed.

Lemma wf_sto_new_typing: forall G s x T ds,
  G & x ~ (typ_bnd T) ~~ s & x ~ (val_new T ds) ->
  G |- trm_val (val_new T ds) : typ_bnd T.
Proof.
  introv Hwf. inversion Hwf.
  - false* empty_push_inv.
  - destruct (eq_push_inv H) as [Hx [HT HG]]. destruct (eq_push_inv H0) as [Hx' [Hv Hs]]. subst.
    assumption.
Qed.

Lemma new_ty_defs: forall G s x T ds,
  G ~~ s ->
  inert G ->
  binds x (val_new T ds) s ->
  exists G' G'',
    G = G' & x ~ (typ_bnd T) & G'' /\
    ty_defs G' x (open_typ x T) (open_defs x ds) (open_typ x T).
Proof.
  introv Hwf Hi Bis.
  assert (exists s' s'', s = s' & x ~ (val_new T ds) & s'') as Hs by (apply* (binds_destruct Bis)).
  destruct Hs as [s' [s'' Hs]].
  lets Bis': (binds_push_eq x (val_new T ds) s').
  lets Hb: (wf_sto_val_new_in_G Hwf Hi Bis).
  destruct (binds_destruct Hb) as [G' [G'' Ht]].
  exists G' G''.
  split. assumption.
  lets Hs': (wf_sto_sub Hwf Ht Hs).
  lets Hw: (wf_sto_new_typing Hs').
  assert (inert G') as Hg'. {
    subst G. apply inert_sub in Hi. apply* inert_sub.
  }
  apply general_to_tight_typing in Hw; auto. apply invertible_lemma_v in Hw; auto.
  apply tpt_to_precise_rec in Hw.
  inversions Hw.
  pick_fresh y.
  rewrite subst_intro_typ with (x:=y). rewrite subst_intro_defs with (x:=y).
  assert (y \notin L) as Hy by auto. specialize (H1 y Hy).
  apply* renaming_def. apply* ok_push. apply* inert_ok. auto. auto.
Qed.

Lemma unfold_rec:
  (forall G t T, G |- t: T -> forall G1 G2 x U,
    ok G ->
    G = G1 & x ~ open_typ x U & G2 ->
    G1 & x ~ typ_bnd U & G2 |- t: T) /\
  (forall G p T, G |-\||/ p: T -> forall G1 G2 x U,
    ok G ->
    G = G1 & x ~ open_typ x U & G2 ->
    G1 & x ~ typ_bnd U & G2 |-\||/ p: T) /\
  (forall G z V d D, G && z ~ V |- d: D -> forall G1 G2 x U,
    ok (G & z ~ V) ->
    G = G1 & x ~ open_typ x U & G2 ->
    G1 & x ~ typ_bnd U & G2 && z ~ V |- d: D) /\
  (forall G z V ds T, G && z ~ V |- ds :: T -> forall G1 G2 x U,
    ok (G & z ~ V) ->
    G = G1 & x ~ open_typ x U & G2 ->
    G1 & x ~ typ_bnd U & G2 && z ~ V |- ds :: T) /\
  (forall G T V, G |- T <: V -> forall G1 G2 x U,
    ok G ->
    G = G1 & x ~ open_typ x U & G2 ->
    G1 & x ~ typ_bnd U & G2 |- T <: V).
Proof.
  apply rules_mutind; intros; subst; eauto.
  - destruct (classicT (x0=x)); subst.
    * apply binds_middle_eq_inv in b. subst.
      apply ty_rec_elim. constructor.
      apply binds_middle_eq. apply (ok_middle_inv_r H). assumption.
    * constructor. apply binds_remove in b. apply* binds_weaken. apply* ok_middle_change.
      auto.
  - (* ty_all_intro *)
    apply_fresh ty_all_intro as z. assert (z \notin L) as Lz by auto.
    specialize (H z Lz G1 (G2 & z ~ T) x U0). repeat rewrite concat_assoc in H.
    apply* H.
  - (* ty_new_intro *)
    apply_fresh ty_new_intro as z. assert (z \notin L) as Lz by auto.
    apply* H.
  - (* ty_let *)
    apply_fresh ty_let as z; auto. assert (z \notin L) as Lz by auto.
    specialize (H0 z Lz G1 (G2 & z ~ T) x U0). repeat rewrite concat_assoc in H0. apply* H0.
  - (* ty_def_trm *)
    constructor. specialize (H G1 (G2 & z ~ U) x U0). repeat rewrite concat_assoc in H.
    apply* H.
  - (* ty_def_val *)
    constructor. specialize (H G1 (G2 & z ~ U) x U0). repeat rewrite concat_assoc in H.
    apply* H.
  - apply_fresh subtyp_all as z; auto. assert (z \notin L) as Lz by auto.
    specialize (H0 z Lz G1 (G2 & z ~ S2) x U). repeat rewrite concat_assoc in H0.
    apply* H0.
Qed.

Lemma corresponding_types_ty_trms: forall G s ds x S a m T',
  G ~~ s ->
  inert G ->
  binds x (typ_bnd S) G ->
  binds x (val_new S ds) s ->
  G |-! trm_path (p_var (avar_f x)) : typ_rcd {a [m] T'} ->
  exists t, defs_has (ds |||^ x) (def_trm a t) /\ G |- t : T'.
Proof.
  introv Hwf Hg Bi Bis Hty.
  pose proof (new_ty_defs Hwf Hg Bis) as [G' [G'' [Heq Htds]]].
  destruct (precise_flow_lemma Hty) as [U Hpf].
  pose proof (inert_typ_bnd_record Hg Bi) as Hrec.
  pose proof (pf_binds Hpf).
  pose proof (binds_func Bi H); subst.
  pose proof (precise_flow_record_has Hg Hpf) as Hrh.
  rewrite <- open_var_path_typ_eq in Hrh.
  pose proof (record_has_ty_defs Htds Hrh) as [d [Hds Htd]].
  assert (Hok: ok (G' & x ~ (S ||^ x))). {
      apply wf_sto_to_ok_G in Hwf. rewrite <- concat_empty_r in *.
      apply* ok_middle_change.
  }
  inversions Htd.
  - exists t. split*. apply* weaken_ty_trm.
    lets Hur: ((proj41 unfold_rec) _ _ _ H5 G' empty x S Hok).
    rewrite concat_empty_r in Hur. specialize (Hur eq_refl). rewrite concat_empty_r in Hur.
    assumption.
  - exists (trm_path p). split*. apply* weaken_ty_trm.
    apply* weaken_ty_trm. admit.
  - exists (trm_val v). split*. apply* weaken_ty_trm.
    lets Hur: ((proj41 unfold_rec) _ _ _ H5 G' empty x S Hok).
    rewrite concat_empty_r in Hur. specialize (Hur eq_refl). rewrite concat_empty_r in Hur.
    assumption.
Qed.

Lemma canonical_forms_2: forall G s x a m T,
  inert G ->
  G ~~ s ->
  G |- trm_path (p_var (avar_f x)) : typ_rcd {a [m] T} ->
  exists S ds t, binds x (val_new S ds) s /\ defs_has (ds |||^ x) (def_trm a t) /\ G |- t : T.
Proof.
  introv Hi Hwf Hty.
  destruct (typing_implies_bound Hty) as [S Bi].
  lets Hty': (general_to_tight_typing Hi Hty).
  lets Hinv: (tight_to_invertible_var Hi Hty').
  destruct (invertible_to_precise_trm_dec Hi Hinv) as [T' [m' [Hx [Heq Hs]]]].
  destruct (corresponding_types Hwf Hi Bi)
    as [[L [U [V [S1 [V1 [t [Hb [Ht [Heq' [Hs1 Hs2]]]]]]]]]] | [U [ds [Hb [Ht Heq']]]]];
    subst.
  - apply pf_bind in Bi. destruct (precise_flow_lemma Hx) as [U' Hr].
    lets Hu: (p_bound_unique Hi Hr Bi). subst. apply precise_flow_all_inv in Hr. inversion Hr.
  - lets Htd: (new_ty_defs Hwf Hi Hb).
    destruct (corresponding_types_ty_trms Hwf Hi Bi Hb Hx) as [t [H1 H2]].
    exists U ds t. split. assumption. split. assumption. apply tight_to_general in Hs; auto.
    apply* ty_sub.
Qed.
