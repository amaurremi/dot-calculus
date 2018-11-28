(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [|-##] and [ty_val_inv], [|-##v]). *)

Set Implicit Arguments.

Require Import Coq.Program.Equality List.
Require Import Sequences.
Require Import Definitions Binding InvertibleTyping Narrowing PreciseTyping RecordAndInertTypes Replacement
        Subenvironments TightTyping Weakening.

(** * Replacement typing
    Whereas invertible typing does replacment for singleton types in one direction,
    replacement typing does the replacment in the other direction.

    Note that we can't simply define this using three rules:
    1) identity from invertible typing
    2) two repl subtyping rules
    The reason is that if we did that, repl typing would necessarily apply the replacement
    in all subterms of a term, whereas we want to be able to say, for example:
    Г ⊢## p: T
    Г ⊢// p: U
    __________
    Г ⊢// p: T ∧ U
*)

Reserved Notation "G '⊢//' p ':' T" (at level 40, p at level 59).

Inductive ty_repl : ctx -> path -> typ -> Prop :=

| ty_inv_r : forall G p T,
    G ⊢## p: T ->
    G ⊢// p: T

| ty_and_r : forall G p T U,
    G ⊢// p: T ->
    G ⊢// p: U ->
    G ⊢// p: typ_and T U

| ty_bnd_r : forall G p T,
    G ⊢// p: open_typ_p p T ->
    G ⊢// p: typ_bnd T

| ty_sel_r : forall G p T q S A,
    G ⊢// p: T ->
    G ⊢! q: S ⪼ typ_rcd {A >: T <: T} ->
    G ⊢// p: typ_path q A

| ty_rec_qp_r : forall G p q r T T' n,
    G ⊢! p : typ_sngl q ⪼ typ_sngl q ->
    G ⊢// r : typ_bnd T ->
    repl_typ n q p T T' ->
    G ⊢// r : typ_bnd T'

| ty_sel_qp_r : forall G p q r r' r'' A n,
    G ⊢! p : typ_sngl q ⪼ typ_sngl q ->
    G ⊢// r : typ_path r' A ->
    repl_typ n q p (typ_path r' A) (typ_path r'' A) ->
    G ⊢// r : typ_path r'' A

| ty_sngl_qp_r : forall G p q r r' r'' n,
    G ⊢! p : typ_sngl q ⪼ typ_sngl q ->
    G ⊢// r : typ_sngl r' ->
    repl_typ n q p (typ_sngl r') (typ_sngl r'') ->
    G ⊢// r : typ_sngl r''

where "G '⊢//' p ':' T" := (ty_repl G p T).

Hint Constructors ty_repl.

Lemma repl_to_precise_trm_dec: forall G p a T,
  inert G ->
  G ⊢// p : typ_rcd {a ⦂ T} ->
  exists T',
    G ⊢!!! p: typ_rcd {a ⦂ T'} /\
    G ⊢# T' <: T.
Proof.
  introv Hi Hinv. dependent induction Hinv. apply* invertible_to_precise_trm_dec.
Qed.

Lemma repl_to_precise_typ_all: forall G p S T,
  inert G ->
  G ⊢// p : typ_all S T ->
  exists S' T' L,
    G ⊢!!! p : typ_all S' T' /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open_typ y T' <: open_typ y T).
Proof.
  introv Hi Hinv. dependent induction Hinv. apply* invertible_to_precise_typ_all.
Qed.

Lemma repl_bot : forall G p,
    inert G ->
    G ⊢// p: typ_bot -> False.
Proof.
  introv Hi Hr. dependent induction Hr; invert_repl; eauto. false* invertible_bot.
Qed.

Lemma repl_to_tight : forall G p T,
    inert G ->
    G ⊢// p : T ->
    G ⊢# trm_path p : T.
Proof.
  introv Hi Hp. induction Hp; try (specialize (IHHp Hi)); eauto. apply* inv_to_tight.
  eapply ty_sub_t. apply IHHp. eauto.
Qed.

Lemma repl_and: forall G p T U,
    inert G ->
    G ⊢// p: typ_and T U ->
    G ⊢// p: T /\ G ⊢// p: U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct (invertible_and Hi H). split*.
Qed.

Lemma replacement_repl_closure_qp : forall G p q r T T' n,
    inert G ->
    G ⊢! q : typ_sngl r ⪼ typ_sngl r ->
    G ⊢// p : T ->
    repl_typ n r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hp.
  gen q r T' n. induction Hp; introv Hq; introv Hr; try solve [invert_repl; eauto 5].
  - Case "ty_inv_r".
    gen q r T' n. induction H; introv Hq; introv Hr; try solve [invert_repl; eauto 5].
    -- SCase "ty_precise_inv".
       destruct (pf3_inertsngl Hi H) as [[Hit | Hs] | Hst].
       + inversions Hit; invert_repl.
         ++ apply ty_inv_r. eapply ty_all_inv.
            apply* ty_precise_inv. apply repl_swap in H6.
            eauto. introv Hy. auto.
         ++ apply ty_inv_r. eapply ty_all_inv.
            apply* ty_precise_inv.
            auto. introv Hy.
            eapply repl_open_var in H6; try solve_names.
            eapply subtyp_sngl_qp. apply* weaken_ty_trm.
            eapply precise_to_general. apply Hq. apply H6.
         ++ apply* ty_rec_qp_r.
       + inversions Hs. invert_repl. eauto.
       + inversion Hst as [x Hx].
         inversions Hx; subst; invert_repl.
         ++ apply ty_inv_r. destruct D2.
            * invert_repl; apply ty_precise_inv in H;
              eapply ty_dec_typ_inv; eauto.
              assert (Hts : G ⊢# t0 <: T1).
              { apply repl_swap in H7. eauto. }
              eauto.
            * invert_repl. eapply ty_precise_inv in H.
              eapply ty_dec_trm_inv; eauto.
        ++ assert (Hpt0 : G ⊢!!! p : T0) by (eapply pf3_and_destruct1; eauto).
           assert (Hpd : G ⊢!!! p : (typ_rcd D)) by (eapply pf3_and_destruct2; eauto).
           apply ty_and_r; eauto.
           admit.
        ++ assert (Hpt0 : G ⊢!!! p : T0) by (eapply pf3_and_destruct1; eauto).
           assert (Hpd : G ⊢!!! p : (typ_rcd D)) by (eapply pf3_and_destruct2; eauto).
          apply ty_and_r; eauto. apply ty_inv_r.
          destruct D2; invert_repl;
          apply ty_precise_inv in Hpd.
          * eapply ty_dec_typ_inv; eauto.
            apply repl_swap in H9. eauto.
          * eapply ty_dec_typ_inv; eauto.
          * eapply ty_dec_trm_inv; eauto.
    -- SCase "ty_dec_trm_inv".
       invert_repl. eapply ty_inv_r. eapply ty_dec_trm_inv.
       apply H. eauto.
    -- SCase "ty_dec_typ_inv".
       invert_repl.
         * eapply ty_inv_r. eapply ty_dec_typ_inv. apply H.
           eapply subtyp_trans_t. apply repl_swap in H10.
           eapply subtyp_sngl_pq_t. eauto.
           apply H10. auto. auto.
         * eapply ty_inv_r. eapply ty_dec_typ_inv. apply H.
           eauto. eapply subtyp_trans_t. apply H1. eauto.
    -- SCase "ty_all_inv".
       invert_repl; apply ty_inv_r.
       + eapply ty_all_inv with (L := L \u (dom G)).
         * apply H.
         * assert (Hts : G ⊢# T3 <: S2).
           { apply repl_swap in H8. eauto. }
           eauto.
         * introv Hy. eapply narrow_subtyping.
           apply H1. eauto.
           assert (Hts : G ⊢ T3 <: S2).
           { apply tight_to_general.
           apply repl_swap in H8. eauto. }
           constructor; eauto. (* narrowing *)
       + eapply ty_all_inv with (L := L \u (dom G)).
         * eauto.
         * assumption.
         * introv Hy. eapply subtyp_trans.
           apply* H1. eapply repl_open_var in H8.
           ** eapply subtyp_sngl_qp; eauto.
              apply precise_to_general in Hq.
              apply weaken_ty_trm; eauto.
           ** apply precise_to_general_h in Hq as [Hq].
              eapply sngl_path_named. apply Hq.
           ** apply precise_to_general_h in Hq as [Hq].
              eapply typed_paths_named. apply Hq.
    -- SCase "ty_sel_qp_inv".
       inversions Hr. eauto.
    -- SCase "ty_sngl_qp_inv".
       inversions Hr. eauto.
  - Case "ty_sel_qp_r".
    lets ?: (ty_sel_qp_r H Hp H0). invert_repl. eauto.
  - Case "ty_sngl_qp_r".
    lets ?: (ty_sngl_qp_r H Hp H0). invert_repl. eauto.
Admitted. (* shelved stuff *)

Lemma replacement_repl_closure_qp2 : forall G p q r T T' n,
    inert G ->
    G ⊢!! q : typ_sngl r ->
    G ⊢// p : T ->
    repl_typ n r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hp Hr. dependent induction Hq.
  - lets Heq: (pf_sngl_T Hi H). subst.
    apply* replacement_repl_closure_qp.
  - lets Hr': (repl_field_elim _ _ _ Hr). eauto.
Qed.

Lemma replacement_repl_closure_qp3 : forall G p q r T T' n,
    inert G ->
    G ⊢!!! q : typ_sngl r ->
    G ⊢// p : T ->
    repl_typ n r q T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hq Hp Hr. gen p T T'. dependent induction Hq; introv Hp Hr.
  - apply* replacement_repl_closure_qp2.
  - specialize (IHHq _ Hi eq_refl).
    destruct (repl_insert q Hr) as [U [Hr1 Hr2]].
    specialize (IHHq _ _ Hp _ Hr1). eapply replacement_repl_closure_qp2.
    auto. apply H. apply IHHq. eauto.
Qed.

Lemma replacement_repl_closure_qp_comp: forall G p q r T T',
    inert G ->
    G ⊢// p: T ->
    G ⊢!!! q: typ_sngl r ->
    repl_repeat_typ r q T T' ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hq Hc. gen p. dependent induction Hc; introv Hp; eauto.
  unfolds repl_some_typ. destruct_all.
  apply* IHHc. apply* replacement_repl_closure_qp3.
Qed.

Lemma repl_rec_intro: forall G p T,
    inert G ->
    G ⊢// p: typ_bnd T ->
    G ⊢// p: open_typ_p p T.
Proof.
  introv Hi Hp. dependent induction Hp; auto.
  - Case "ty_inv_r".
    destruct* (invertible_bnd Hi H) as [Hr | [q [Hr Hr']]].
    eapply replacement_repl_closure_qp_comp. auto. apply* ty_inv_r.
    apply Hr.
    apply* repl_comp_open.
  - Case "ty_rec_pq_r".
    specialize (IHHp _ Hi eq_refl).
    apply repl_open with (r:= r) in H0; try solve_names. apply* replacement_repl_closure_qp.
Qed.

(*
  G ⊢// r: T[q1 / p1, n]
  G ⊢!!! p2: q2.type
  n <> m
  __________________________________
  G ⊢// r: T[p2 / q2, m][q1 / p1, n]
*)
Lemma replacement_swap_closure: forall G r q1 p1 T T1 p2 q2 T2 T21 n m,
    inert G ->
    repl_typ n p1 q1 T T1 ->
    G ⊢// r: T1 ->
    G ⊢! p2: typ_sngl q2 ⪼ typ_sngl q2 ->
    repl_typ m q2 p2 T T2 ->
    repl_typ n p1 q1 T2 T21 ->
    n <> m ->
    G ⊢// r: T21.
Proof.
  introv Hi HTT1 Hr1 Hp2 HTT2 HT2T21 Hn.
  destruct (repl_preserved2 HTT1 HTT2 Hn) as [V HV].
  lets Hc: (replacement_repl_closure_qp Hi Hp2 Hr1 HV).
  lets Heq: (repl_order_swap HTT1 HV Hn HTT2 HT2T21). subst*.
Qed.

Lemma replacement_repl_closure_pq_helper : forall G r q1 p1 T T1 p2 q2 T2 n,
    inert G ->
    G ⊢// r: T ->
    G ⊢! p1: typ_sngl q1 ⪼ typ_sngl q1 ->
    G ⊢! p2: typ_sngl q2 ⪼ typ_sngl q2 ->
    repl_typ n q1 p1 T T1 ->
    repl_typ n p2 q2 T1 T2 ->
    G ⊢// r: T2.
Proof.
  introv Hi Hr Hp1 Hp2 Hr1 Hr2.
  destruct (repl_prefixes Hr1 Hr2) as [bs [Heq | Heq]].
  - subst. assert (bs = nil) as Heq by apply* pf_sngl_flds_elim. subst.
    rewrite field_sel_nil in *.
    lets Hu: (pf_T_unique Hi Hp1 Hp2). inversions Hu. apply repl_swap in Hr1.
    lets Heq: (repl_unique Hr1 Hr2). subst*.
  - subst. assert (bs = nil) as Heq. {
      eapply pf_sngl_flds_elim. apply Hi. apply Hp1. apply Hp2.
    }
    subst. rewrite field_sel_nil in *.
    lets Hu: (pf_T_unique Hi Hp1 Hp2). inversions Hu.
    apply repl_swap in Hr1.
    lets Heq: (repl_unique Hr1 Hr2). subst*.
Qed.

Lemma replacement_repl_closure_pq : forall G p q r n T T',
    inert G ->
    G ⊢// p : T ->
    G ⊢! q : typ_sngl r ⪼ typ_sngl r ->
    repl_typ n q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hqr.
  gen q r n T'. induction Hp; introv Hq; introv Hr; eauto.
   - Case "ty_inv_r".
     constructor. apply* invertible_repl_closure.
   - Case "ty_and_r".
     invert_repl; eauto.
   - Case "ty_bnd_r".
     invert_repl. apply (repl_open p) in H3; try solve_names. eauto.
   - Case "ty_sel_r".
     clear IHHp. invert_repl. lets Heq: (pf_sngl_flds_elim _ Hi Hq H). subst.
     rewrite field_sel_nil in *.
     lets Heq: (pf_T_unique Hi H Hq). subst.
     apply pf_sngl_U in H. inversion H.
  - Case "ty_rec_qp_r".
    invert_repl. specialize (IHHp Hi _ _ Hq).
    destruct (classicT (n=n0)).
    * subst. specialize (IHHp n0).
      apply* (replacement_repl_closure_pq_helper Hi Hp H Hq (rbnd H0) (rbnd H5)).
    * destruct (repl_preserved1 H0 H5 n1) as [V Hv]. apply rbnd in Hv.
      specialize (IHHp _ _ Hv).
      eapply (replacement_swap_closure Hi Hv IHHp H); eauto.
  - Case "ty_sel_pq_r".
    specialize (IHHp Hi _ _ Hq 0).
    assert (n0 = 0) as Heq by inversion* Hr. assert (n = 0) as Heq' by inversion* H0. subst.
    eapply (replacement_repl_closure_pq_helper Hi Hp H Hq); eauto.
  - Case "ty_sngl_pq_r".
    specialize (IHHp Hi _ _ Hq 0).
    assert (n0 = 0) as Heq by inversion* Hr. assert (n = 0) as Heq' by inversion* H0. subst.
    eapply (replacement_repl_closure_pq_helper Hi Hp H Hq); eauto.
Qed.

Lemma replacement_repl_closure_pq2 : forall G p q r T T' n,
    inert G ->
    G ⊢// p : T ->
    G ⊢!! q : typ_sngl r ->
    repl_typ n q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hq Hr. dependent induction Hq.
  - apply* replacement_repl_closure_pq. lets Heq: (pf_sngl_T Hi H). subst. auto.
  - lets Hr': (repl_field_elim _ _ _ Hr).
    eauto.
Qed.

Lemma replacement_repl_closure_pq3 : forall G p q r T T' n,
    inert G ->
    G ⊢// p : T ->
    G ⊢!!! q : typ_sngl r ->
    repl_typ n q r T T' ->
    G ⊢// p : T'.
Proof.
  introv Hi Hp Hq Hr. gen p T. dependent induction Hq; introv Hp Hr.
  - apply* replacement_repl_closure_pq2.
  - destruct (repl_insert q Hr) as [U [Hr1 Hr2]].
    lets Hc: (replacement_repl_closure_pq2 Hi Hp H Hr1). apply* IHHq.
Qed.

Lemma replacement_repl_closure_pq_comp: forall G p q r T T',
    inert G ->
    G ⊢// p: T ->
    G ⊢!!! q: typ_sngl r ->
    repl_repeat_typ q r T T' ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hq Hc. gen p. dependent induction Hc; introv Hp; eauto.
  unfolds repl_some_typ. destruct_all.
  apply* IHHc. apply* replacement_repl_closure_pq3.
Qed.

Lemma path_sel_repl2: forall G p A T q,
    inert G ->
    G ⊢!! p : typ_rcd {A >: T <: T} ->
    G ⊢// q : T ->
    G ⊢// q : typ_path p A.
Proof.
  introv Hi Hp Hq. dependent induction Hp; eauto.
Qed.

Lemma path_sel_repl: forall G p A T q,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢// q : T ->
    G ⊢// q : typ_path p A.
Proof.
  introv Hi Hp Hq. dependent induction Hp; eauto.
  apply* path_sel_repl2.
  specialize (IHHp _ _ Hi eq_refl Hq).
  assert (forall q, q = q •• nil) as Hnil. {
    intro. rewrite* field_sel_nil.
  }
  lets He1: (Hnil q0). lets He2: (Hnil p).
  eapply (replacement_repl_closure_qp2 Hi H IHHp).
  rewrite He1 at 2. rewrite He2 at 2. apply rpath.
Qed.

Lemma path_sel_repl_inv: forall G p A T q,
    inert G ->
    G ⊢!!! p : typ_rcd {A >: T <: T} ->
    G ⊢// q : typ_path p A ->
    G ⊢// q : T.
Proof.
  introv Hi Hp Hq. dependent induction Hq.
  - Case "ty_inv_r".
    constructor. apply* path_sel_inv.
  - Case "ty_sel_r".
    clear IHHq. lets Heq: (pf_pt3_unique Hi H Hp). subst*.
  - Case "ty_sel_qp_r".
    destruct (repl_prefixes_sel H0) as [bs [He1 He2]].
    subst. assert (record_type (typ_rcd {A >: T <: T})) as Hrt by eauto.
    lets Hqbs: (pf_pt3_trans_inv_mult' _ Hi H Hp (or_intror Hrt)). apply* IHHq.
Qed.

Lemma replacement_subtyping_closure : forall G T U p,
    inert G ->
    G ⊢# T <: U ->
    G ⊢// p: T ->
    G ⊢// p: U.
Proof.
  introv Hi Hs. gen p. induction Hs; introv Hp; auto.
  - Case "subtyp_top".
    induction Hp; eauto.
  - Case  "subtyp_bot".
    false* repl_bot.
  - Case "subtyp_and1".
    apply (repl_and Hi) in Hp. destruct_all. auto.
  - Case "subtyp_and2".
    apply (repl_and Hi) in Hp. destruct_all. auto.
  - Case "subtyp_fld".
    dependent induction Hp; eauto.
  - Case "subtyp_typ".
    dependent induction Hp; eauto.
  - Case "subtyp_sngl_pq".
    apply* replacement_repl_closure_pq3.
  - Case "subtyp_sngl_qp".
    apply* replacement_repl_closure_qp3.
  - Case "subtyp_sel2".
    apply* path_sel_repl.
  - Case "subtyp_sel1".
    apply* path_sel_repl_inv.
  - Case "subtyp_all".
    dependent induction Hp; eauto.
Qed.

Lemma repl_fld : forall G p a T,
    inert G ->
    G ⊢// p: typ_rcd {a ⦂ T} ->
    G ⊢// p•a : T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  dependent induction H; eauto.
  - dependent induction H.
    * dependent induction H; eauto.
      apply pf_fld in H; apply ty_inv_r; apply* ty_precise_inv.
    * lets Hq: (pt3_field_elim H0).
      lets Hp: (pt3_trans _ H Hq). eauto.
  - specialize (IHty_path_inv _ _ eq_refl Hi). apply ty_inv_r in H.
    eapply replacement_subtyping_closure. auto. apply H0. auto.
Qed.

Lemma repl_prec_exists: forall G p T,
    G ⊢// p: T ->
    exists U, G ⊢!!! p: U.
Proof.
  induction 1; auto.  induction H; eauto.
Qed.

Lemma replacement_repl_closure_comp_typed: forall G p T T',
    inert G ->
    G ⊢// p: T ->
    repl_composition_qp G T T' ->
    G ⊢// p: T'.
Proof.
  introv Hi Hp Hr. dependent induction Hr; eauto.
  destruct H as [p' [q' [n [Hpq Hr']]]].
  lets Hrc: (replacement_repl_closure_qp Hi Hpq Hp Hr'). eauto.
Qed.

Lemma repl_to_invertible_sngl_repl_comp: forall G p q,
    inert G ->
    G ⊢// p: typ_sngl q ->
    exists q', repl_composition_qp G (typ_sngl q') (typ_sngl q) /\ G ⊢## p: typ_sngl q'.
Proof.
  introv Hi Hp. dependent induction Hp.
  - Case "ty_inv_r".
    exists q. split*. apply star_refl.
  - Case "ty_sngl_qp_r".
    specialize (IHHp _ Hi eq_refl). destruct IHHp as [p' [Hr Hr']].
    eexists. split*. eapply star_trans. apply Hr.  apply star_one. repeat eexists. eauto. apply H0.
Qed.

Lemma repl_to_invertible_sngl: forall G p q,
    inert G ->
    G ⊢// p: typ_sngl q ->
    exists q', G ⊢## p: typ_sngl q' /\ (q = q' \/ G ⊢!!! q: typ_sngl q').
Proof.
  introv Hi Hp. destruct (repl_to_invertible_sngl_repl_comp Hi Hp) as [r [Hrc Hpq]].
  destruct (inv_to_precise_sngl Hi Hpq) as [r' [Hrc' [Heq | Hpq']]].
  - subst. exists r. destruct (sngl_typed3 Hi Hrc'). destruct* (repl_comp_typed Hi Hrc H).
    split*. eapply repl_comp_to_prec. auto. auto. apply H0.
  - eexists. split*. destruct (sngl_typed3 Hi Hpq') as [r1 Ht].
    destruct (repl_comp_typed Hi Hrc Ht) as [r2 Ht2]. apply* repl_comp_to_prec.
Qed.

Lemma path_elim_repl: forall G p q a T,
    inert G ->
    G ⊢// p: typ_sngl q ->
    G ⊢// q•a : T ->
    G ⊢// p•a : typ_sngl q•a.
Proof.
  introv Hi Hp Hq.
  destruct (repl_to_invertible_sngl_repl_comp Hi Hp) as [p' [Hc Hpi]].
  destruct (repl_comp_sngl_inv1 Hc) as [r Heq]. inversions Heq.
  destruct (inv_to_precise_sngl_repl_comp Hpi) as [r' [Hp' Hrc]].
  destruct (repl_prec_exists Hq) as [U Hq']. clear Hq.
  destruct (field_typing_comp1 _ Hi Hc Hq') as [T1 Hra].
  destruct (field_typing_comp2 _ Hi Hrc Hra) as[T2 Hr'a].
  lets Hper: (path_elim_prec _ Hi Hp' Hr'a).
  lets Hinv: (ty_precise_inv Hper).
  assert (repl_composition_qp G (typ_sngl r • a) (typ_sngl r' • a)) as Hr'
    by apply* repl_composition_fld_elim.
  assert (repl_composition_qp G (typ_sngl r • a) (typ_sngl q • a)) as Hr''
   by apply* repl_composition_fld_elim.
  lets Hic: (invertible_repl_closure_comp_typed Hi Hinv Hr').
  apply* replacement_repl_closure_comp_typed.
Qed.

Lemma repl_top: forall G r T,
    G ⊢// r: T ->
    G ⊢// r: typ_top.
Proof.
  introv Hr. induction Hr; eauto.
Qed.

Lemma inv_sngl_trans: forall G p q T,
    inert G ->
    G ⊢// p : typ_sngl q ->
    G ⊢## q : T ->
    G ⊢// p : T.
Proof.
  introv Hi Hpq Hq. gen p. induction Hq; introv Hpq; eauto; try solve [apply* replacement_repl_closure_pq].
  - destruct (repl_to_invertible_sngl Hi Hpq) as [r [Hpr Hrc]].
    destruct (inv_to_precise_sngl Hi Hpr) as [r' [Hpr' Hrc']]. clear Hpr Hpq.
    destruct Hrc, Hrc'; subst.
    * do 2 constructor. apply* pt3_sngl_trans3.
    * do 2 constructor. repeat apply* pt3_sngl_trans3.
    * lets Hpi: (pt3_invert Hi H H0). destruct_all; subst; auto.
      ** do 2 constructor. apply* pt3_sngl_trans3.
      ** apply ty_precise_inv in Hpr'. apply ty_inv_r in Hpr'.
         apply* replacement_repl_closure_qp3. apply* repl_intro_sngl.
    * lets Hpi: (pt3_invert Hi H H0). destruct_all; subst.
      ** do 2 constructor. do 2 apply* pt3_sngl_trans3.
      ** do 2 constructor. apply* pt3_sngl_trans3.
      ** apply ty_precise_inv in Hpr'. apply ty_inv_r in Hpr'.
         lets Hc: (replacement_repl_closure_pq3 Hi Hpr' H1 (repl_intro_sngl r' r)).
         apply* replacement_repl_closure_qp3. apply* repl_intro_sngl.
  - eapply (replacement_subtyping_closure Hi). eapply subtyp_fld_t.
    apply H. auto.
  - eapply (replacement_subtyping_closure Hi). eapply subtyp_typ_t.
    apply H. apply H0. auto.
  - eapply (replacement_subtyping_closure Hi). eapply subtyp_all_t.
    apply H. apply H0. auto.
  - apply* repl_top.
Qed.

Lemma repl_sngl_trans: forall G p q T,
    inert G ->
    G ⊢// p : typ_sngl q ->
    G ⊢// q : T ->
    G ⊢// p : T.
Proof.
  introv Hi Hpq Hq. gen p. induction Hq; introv Hpq; eauto.
  - apply* inv_sngl_trans.
  - specialize (IHHq Hi _ Hpq). apply ty_bnd_r.
    destruct (repl_to_invertible_sngl Hi Hpq) as [r [Hpr Hor]].
    destruct (inv_to_precise_sngl Hi Hpr) as [r' [Hpr' Hor']]. clear Hpr Hpq.
    destruct Hor, Hor'; subst.
    * assert (repl_repeat_typ r p0 (open_typ_p r T) (open_typ_p p0 T)) as Hrr by apply* repl_comp_open_rec.
      apply* replacement_repl_closure_qp_comp.
    * assert (repl_repeat_typ r r' (open_typ_p r T) (open_typ_p r' T)) as Hrr by apply* repl_comp_open_rec.
      lets Hc: (replacement_repl_closure_qp_comp Hi IHHq H0 Hrr).
      eapply (replacement_repl_closure_qp_comp Hi Hc). apply Hpr'. apply* repl_comp_open_rec.
    * assert (repl_repeat_typ p r (open_typ_p p T) (open_typ_p r T)) as Hrr by apply* repl_comp_open_rec.
      lets Hc: (replacement_repl_closure_pq_comp Hi IHHq H Hrr).
      apply* replacement_repl_closure_qp_comp. apply* repl_comp_open_rec.
    * assert (repl_repeat_typ p r (open_typ_p p T) (open_typ_p r T)) as Hrr by apply* repl_comp_open_rec.
      lets Hc: (replacement_repl_closure_pq_comp Hi IHHq H Hrr).
      assert (repl_repeat_typ r r' (open_typ_p r T) (open_typ_p r' T)) as Hrr' by apply* repl_comp_open_rec.
      lets Hc': (replacement_repl_closure_qp_comp Hi Hc H0 Hrr').
      eapply (replacement_repl_closure_qp_comp Hi). apply Hc'. apply Hpr'. apply* repl_comp_open_rec.
Qed.

Lemma replacement_closure : forall G p T,
  inert G ->
  G ⊢# trm_path p : T ->
  G ⊢// p: T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  - Case "ty_var_t".
    repeat econstructor; eauto.
  - Case "ty_new_elim_t".
    apply* repl_fld.
  - Case "ty_sngl_t".
    apply* repl_sngl_trans.
  - Case "ty_path_elim_t".
    apply* path_elim_repl.
  - Case "ty_rec_elim_t".
    specialize (IHHp _ Hi eq_refl). apply* repl_rec_intro.
  - Case "ty_sub_t".
    specialize (IHHp _ Hi eq_refl).
    eapply replacement_subtyping_closure. auto. apply H. auto.
Qed.

(** Replacement typing for values *)

Reserved Notation "G '⊢//v' v ':' T" (at level 40, v at level 59).

Inductive ty_replv : ctx -> val -> typ -> Prop :=

| ty_inv_rv : forall G v T,
    G ⊢##v v: T ->
    G ⊢//v v: T

| ty_and_rv : forall G v T U,
    G ⊢//v v: T ->
    G ⊢//v v: U ->
    G ⊢//v v: typ_and T U

| ty_sel_rv : forall G v T q S A,
    G ⊢//v v: T ->
    G ⊢! q: S ⪼ typ_rcd {A >: T <: T} ->
    G ⊢//v v: typ_path q A

| ty_rec_qp_rv : forall G p q v T T' n,
    G ⊢! p : typ_sngl q ⪼ typ_sngl q ->
    G ⊢//v v : typ_bnd T ->
    repl_typ n q p T T' ->
    G ⊢//v v : typ_bnd T'

| ty_sel_qp_rv : forall G p q v r' r'' A n,
    G ⊢! p : typ_sngl q ⪼ typ_sngl q ->
    G ⊢//v v : typ_path r' A ->
    repl_typ n q p (typ_path r' A) (typ_path r'' A) ->
    G ⊢//v v : typ_path r'' A

where "G '⊢//v' v ':' T" := (ty_replv G v T).

Hint Constructors ty_replv.

Lemma invertible_andv: forall G v T U,
    inert G ->
    G ⊢##v v: typ_and T U ->
    G ⊢##v v: T /\ G ⊢##v v: U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. inversion H.
Qed.

Lemma repl_andv: forall G v T U,
    inert G ->
    G ⊢//v v: typ_and T U ->
    G ⊢//v v: T /\ G ⊢//v v: U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct (invertible_andv Hi H). split*.
Qed.

Lemma replacement_value_repl_closure_pq : forall G p q r n T T',
    inert G ->
    G ⊢//v p : T ->
    G ⊢! q : typ_sngl r ⪼ typ_sngl r ->
    repl_typ n q r T T' ->
    G ⊢//v p : T'.
Proof.
Admitted.

Lemma replacement_value_repl_closure_pq2 : forall G p q r T T' n,
    inert G ->
    G ⊢//v p : T ->
    G ⊢!! q : typ_sngl r ->
    repl_typ n q r T T' ->
    G ⊢//v p : T'.
Proof.
  introv Hi Hp Hq Hr. dependent induction Hq.
  - apply* replacement_value_repl_closure_pq. lets Heq: (pf_sngl_T Hi H). subst. auto.
  - lets Hr': (repl_field_elim _ _ _ Hr).
    eauto.
Qed.

Lemma replacement_value_repl_closure_pq3 : forall G p q r T T' n,
    inert G ->
    G ⊢//v p : T ->
    G ⊢!!! q : typ_sngl r ->
    repl_typ n q r T T' ->
    G ⊢//v p : T'.
Proof.
  introv Hi Hp Hq Hr. gen p T. dependent induction Hq; introv Hp Hr.
  - apply* replacement_value_repl_closure_pq2.
  - destruct (repl_insert q Hr) as [U [Hr1 Hr2]].
    lets Hc: (replacement_value_repl_closure_pq2 Hi Hp H Hr1). apply* IHHq.
Qed.

Lemma replacement_value_repl_closure_pq_comp: forall G p q r T T',
    inert G ->
    G ⊢//v p: T ->
    G ⊢!!! q: typ_sngl r ->
    repl_repeat_typ q r T T' ->
    G ⊢//v p: T'.
Proof.
  introv Hi Hp Hq Hc. gen p. dependent induction Hc; introv Hp; eauto.
  unfolds repl_some_typ. destruct_all.
  apply* IHHc. apply* replacement_value_repl_closure_pq3.
Qed.

(* TODO *)
Lemma replacement_value_repl_closure_qp:
  forall G v p q T T' n,
    inert G ->
    G ⊢! p : typ_sngl q ⪼ typ_sngl q ->
    G ⊢//v v : T ->
    repl_typ n q p T T' ->
    G ⊢//v v : T'.
Proof.
  introv Hi Hpq Hv.
  gen p q T' n. induction Hv; introv Hpq; introv Hr.
  - Case "ty_inv_rv".
    gen p q T' n. induction H; introv Hpq; introv Hr;
    try solve [invert_repl; eauto].
    -- admit.
    -- invert_repl.
      + constructor. admit.
      + admit.
  - Case "ty_and_rv".
    invert_repl; eauto.
  - Case "ty_sel_rv".
    invert_repl; eauto.
  - Case "ty_rec_qp_rv".
    invert_repl; eauto.
  - Case "ty_sel_qp_rv".
    lets ?: (ty_sel_qp_rv H Hv H0).
    invert_repl; eauto.
Admitted.

Lemma replacement_value_repl_closure_qp2 : forall G p q r T T' n,
    inert G ->
    G ⊢!! q : typ_sngl r ->
    G ⊢//v p : T ->
    repl_typ n r q T T' ->
    G ⊢//v p : T'.
Proof.
  introv Hi Hq Hp Hrq. dependent induction Hq.
  - lets Heq: (pf_sngl_T Hi H). subst.
    apply* replacement_value_repl_closure_qp.
  - lets Hr': (repl_field_elim _ _ _ Hrq). eauto.
Qed.

Lemma replacement_value_repl_closure_qp3 : forall G p q r T T' n,
    inert G ->
    G ⊢!!! q : typ_sngl r ->
    G ⊢//v p : T ->
    repl_typ n r q T T' ->
    G ⊢//v p : T'.
Proof.
  introv Hi Hq Hp Hr. gen p T T'. dependent induction Hq; introv Hp Hr.
  - apply* replacement_value_repl_closure_qp2.
  - specialize (IHHq _ Hi eq_refl).
    destruct (repl_insert q Hr) as [U [Hr1 Hr2]].
    specialize (IHHq _ _ Hp _ Hr1). eapply replacement_value_repl_closure_qp2.
    auto. apply H. apply IHHq. eauto.
Qed.

Lemma replacement_value_repl_closure_qp_comp: forall G p q r T T',
    inert G ->
    G ⊢//v p: T ->
    G ⊢!!! q: typ_sngl r ->
    repl_repeat_typ r q T T' ->
    G ⊢//v p: T'.
Proof.
  introv Hi Hp Hq Hc. gen p. dependent induction Hc; introv Hp; eauto.
  unfolds repl_some_typ. destruct_all.
  apply* IHHc. apply* replacement_value_repl_closure_qp3.
Qed.

Lemma invertible_typing_closure_tight_v: forall G v T U,
  inert G ->
  G ⊢//v v : T ->
  G ⊢# T <: U ->
  G ⊢//v v : U.
Proof.
  introv Hi HT Hsub.
  induction Hsub; auto.
  - dependent induction HT; eauto.
  - dependent induction HT. dependent induction H. inversion H.
  - destruct* (repl_andv Hi HT).
  - destruct* (repl_andv Hi HT).
  - dependent induction HT. dependent induction H. dependent induction H.
  - dependent induction HT. dependent induction H. dependent induction H.
  - apply* replacement_value_repl_closure_pq3.
    (* repl closure for vals *)
  - apply* replacement_value_repl_closure_qp3.
    (* repl closure for vals *)
  - admit.
  - admit.
  - dependent induction HT. constructor*.
Admitted.

Lemma replacement_closure_v : forall G v T,
    inert G ->
    G ⊢# trm_val v : T ->
    G ⊢//v v : T.
Proof.
  introv Hgd Hty.
  dependent induction Hty; eauto.
  specialize (IHHty v Hgd eq_refl).
  apply* invertible_typing_closure_tight_v.
Qed.

Lemma repl_to_invertible_obj G T U ds :
  inert G ->
  G ⊢//v val_new T ds : typ_bnd U ->
  exists U', G ⊢##v val_new T ds : typ_bnd U' /\ repl_composition_qp G U' U.
Proof.
  intros Hi Hv. dependent induction Hv.
  - exists U. split*. constructor.
  - specialize (IHHv _ _ _ Hi eq_refl eq_refl) as [U' [Hinv Hrc]].
    eexists. split.
    * eauto.
    * eapply star_trans. apply Hrc. apply star_one. econstructor. repeat eexists.
      apply H. eauto.
Qed.

Lemma invertible_to_precise_obj G T U ds :
  inert G ->
  G ⊢##v val_new T ds : typ_bnd U ->
  G ⊢!v val_new T ds : typ_bnd T /\ repl_composition_qp G U T.
Proof.
  intros Hi Hv. dependent induction Hv.
  - inversions H. split*. constructor.
  - specialize (IHHv _ _ _ Hi eq_refl eq_refl) as [Hinv Hrc].
    split.
    * eauto.
    * eapply star_trans. apply star_one. econstructor. repeat eexists. apply H. apply* repl_swap.
      apply Hrc.
Qed.
