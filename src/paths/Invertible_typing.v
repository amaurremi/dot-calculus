Set Implicit Arguments.

Require Import LibLN.
Require Import Coq.Program.Equality.
Require Import Definitions.
Require Import Inert_types.
Require Import Some_lemmas.
Require Import Narrowing.

(* ****************************************** *)
(* Invertible to precise *)

Lemma invertible_to_precise_typ_dec: forall G p A S U,
    inert G ->
    G |-## p : typ_rcd { A >: S <: U } ->
    exists T,
      G |-! trm_path p : typ_rcd { A >: T <: T } /\
      G |-# T <: U /\
      G |-# S <: T.
Proof.
  introv HG Ht.
  dependent induction Ht.
  - lets Hp: (precise_dec_typ_inv HG H). subst.
    exists U. split*.
  - specialize (IHHt A T U0 HG eq_refl). destruct IHHt as [V [Hx [Hs1 Hs2]]].
    exists V. split*.
Qed.

Lemma invertible_to_precise_trm_dec: forall G p a m T,
    inert G ->
    G |-## p : typ_rcd { a [m] T } ->
    exists T' m',
      G |-! trm_path p : typ_rcd { a [m'] T' } /\
      (m = strong -> m' = strong /\ T = T') /\
      G |-# T' <: T.
Proof.
  introv Hi Ht. dependent induction Ht.
  - (* t_pt_precise *)
    exists T m. auto.
  - (* t_pt_dec_trm *)
    specialize (IHHt _ _ _ Hi eq_refl). destruct IHHt as [V [m [Hp [Eq Hs]]]].
    exists V m. split*. split. intros F. inversion F. apply* subtyp_trans_t.
  - (* t_pt_dec_trm_strong *)
    specialize (IHHt _ _ _ Hi eq_refl). destruct IHHt as [V [m [Hp [Eq Hs]]]].
    specialize (Eq eq_refl). destruct Eq as [Eq1 Eq2]. subst.
    exists V strong. split*.
Qed.

Lemma invertible_to_precise_typ_all: forall G p S T,
    inert G ->
    G |-## p : typ_all S T ->
    exists S' T' L,
      G |-! trm_path p : typ_all S' T' /\
      G |-# S <: S' /\
      (forall y,
          y \notin L ->
              G & y ~ S |- T' ||^ y <: T ||^ y).
Proof.
  introv Hi Ht. dependent induction Ht.
  - exists S T (dom G); auto.
  - specialize (IHHt _ _ Hi eq_refl).
    destruct IHHt as [S' [T' [L' [Hpt [HSsub HTsub]]]]].
    exists S' T' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : G |-# typ_all S0 T0 <: typ_all S T) by (apply* subtyp_all_t). split.
    + eapply subtyp_trans_t; eauto.
    + intros y Fr.
      assert (Hok: ok (G & y ~ S)) by auto using ok_push, inert_ok.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ S |- T' ||^ y <: T0 ||^ y).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

Lemma invertible_to_precise_sngl: forall G p q,
    inert G ->
    G |-## p: typ_sngl q ->
    G |-! trm_path p: typ_sngl q \/ p = q.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
Qed.

Lemma invertible_sub_closure: forall G p T U,
  inert G ->
  G |-## p : T ->
  G |-# T <: U ->
  G |-## p : U.
Proof.
  introv Hi HT Hsub. gen p. induction Hsub; introv HT; eauto.
  - (* subtyp_bot_t *)
    inversions HT. false* precise_bot_false.
  - (* subtyp_and1_t *)
    inversion* HT.
  - (* subtyp_and2_t *)
    inversion* HT.
  - (* subtyp_sel2t *)
    inversions HT.
    + (* ty_path_i *)
      false* precise_psel_false.
    + (* subtyp_sel_i *)
      lets Hu: (inert_unique_tight_bounds Hi H H5). subst*.
    + (* subtyp_sel1_t *)
      lets Hu: (p_sngl_unique Hi H2 H). inversion Hu.
  - (* subtyp_sel2_t *)
    inversions HT.
    + false* precise_psel_false.
    + lets Hu: (p_sngl_unique Hi H H6). inversion Hu.
    + lets Hu: (p_sngl_unique Hi H H3). inversions Hu. assumption.
  - (* subtyp_sngl_sel2_t *)
    inversions HT.
    + false* precise_psel_false.
    + lets Hs: (subtyp_sel_i H5 H6).
      destruct (classicT (p = q)) as [Heq | Hneq].
      * subst*.
      * apply* subtyp_sngl_i.
    + destruct (classicT (p = q)) as [Heq | Hneq]. subst*. apply* subtyp_sngl_i.
Qed.

Lemma tight_to_invertible_var: forall G x T,
    inert G ->
    G |-# trm_path (p_var (avar_f x)): T ->
    G |-## p_var (avar_f x) : T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  - specialize (IHHp _ Hi eq_refl). inversions IHHp; auto.
    apply ty_rec_elim_p in H. constructor*. rewrite* open_var_path_typ_eq.
  - specialize (IHHp _ Hi eq_refl). apply* invertible_sub_closure.
Qed.

Lemma tight_to_invertible_p: forall G p T,
    inert G ->
    G |-#\||/ p: T ->
    G |-## p: T.
Proof.
  introv Hi Hp.
  induction Hp; try (specialize (IHHp Hi)).
  - apply* tight_to_invertible_var.
  - inversions IHHp; auto. rewrite* <- open_var_path_typ_eq.
  - inversions IHHp; auto. apply ty_and1_p in H. constructor*.
  - inversions IHHp; auto. apply ty_and2_p in H. constructor*.
  - inversions IHHp. apply ty_fld_elim_p in H0; auto.
  - apply* invertible_sub_closure.
Qed.

Lemma invertible_sub_closure_v: forall G v T U,
  inert G ->
  G |-##v v: T ->
  G |-# T <: U ->
  G |-##v v : U.
Proof.
  introv Hi HT Hsub.
  dependent induction Hsub; eauto; inversions HT; try solve [inversion H]; try assumption.
  - inversion H0.
  - lets Hb: (inert_unique_tight_bounds Hi H H5). subst*.
  - lets Hu: (p_sngl_unique Hi H5 H). inversion Hu.
  - inversion H1.
  - lets Hb: (p_sngl_unique Hi H H6). inversion Hb.
  - lets Hb: (p_sngl_unique Hi H6 H). inversions Hb. assumption.
Qed.

Lemma invertible_lemma_v : forall G v T,
    inert G ->
    G |-# trm_val v : T ->
    G |-##v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty _ Hgd eq_refl).
  apply* invertible_sub_closure_v.
Qed.
