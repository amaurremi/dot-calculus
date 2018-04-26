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
  introv Hi Hq Hp. gen q r T' n. induction Hp; introv Hq; introv Hr; invert_repl; eauto 5.
  gen q r T' n. induction H; introv Hq; introv Hr; try solve [invert_repl; eauto 5].
  -  Case "ty_precise_inv".
     destruct (pf3_inertsngl Hi H) as [[Hit | Hs] | Hst].
     + inversions Hit; invert_repl.
       ++ apply ty_inv_r. eapply ty_all_inv. apply* ty_precise_inv.
          apply repl_swap in H6. eauto. introv Hy. auto.
       ++ apply ty_inv_r.
          eapply ty_all_inv. apply* ty_precise_inv.
          auto. introv Hy. eapply repl_open_var in H6; try solve_names.
          eapply subtyp_sngl_qp. apply* weaken_ty_trm. eapply precise_to_general. apply Hq.
          apply H6.
       ++ apply* ty_rec_qp_r.
     + inversions Hs. invert_repl. eauto.
     +  admit. (* inverstion on record type and usual stuff *)
  - Case "ty_dec_trm_inv".
    invert_repl. eapply ty_inv_r. eapply ty_dec_trm_inv. apply H.
    eauto.
  - Case "ty_dec_typ_inv".
    invert_repl.
    * eapply ty_inv_r. eapply ty_dec_typ_inv. apply H.
      eapply subtyp_trans_t. apply repl_swap in H10. eapply subtyp_sngl_pq_t. eauto.
      apply H10. auto. auto.
    * eapply ty_inv_r. eapply ty_dec_typ_inv. apply H.
      eauto. eapply subtyp_trans_t. apply H1. eauto.
  - Case "ty_all_inv".
    invert_repl; apply ty_inv_r; eapply ty_all_inv. apply H.
    admit. (* simple *)
    introv Hy. admit. (* narrowing *)
    apply H. auto. introv Hy. eapply subtyp_trans. apply* H1.
    eapply repl_open_var in H8; admit. (* simple *)
  - Case "ty_sel_qp_inv".
    inversions Hr. eauto.
  - Case "ty_sngl_qp_inv".
    inversions Hr. eauto.
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
    assert (exists bs, p = p0 •• bs /\ r' = q •• bs) as [bs [Heq1 Heq2]]. {
      inversions H0. eexists. split*.
    }
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

Lemma repl_comp_typed : forall G p q T,
    inert G ->
    repl_composition_qp G (typ_sngl q) (typ_sngl p) ->
    G ⊢!!! q: T ->
    exists U, G ⊢!!! p: U.
Proof.
  introv Hi Hr Hq. gen T. dependent induction Hr; introv Hq; eauto.
  assert (exists q', b = typ_sngl q') as [q' Heq] by admit. subst.
  destruct H as [r [r' [n [H2 H3]]]].
  destruct (repl_prefixes_sngl H3) as [bs [He1 He2]]. subst.
  apply* IHHr. apply* pt3_field_trans'.
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

Lemma sngl_inert_sngl: forall q, inert_sngl (typ_sngl q).
Proof.
  introv. right. eexists. eauto.
Qed.

Lemma pt23_invert : forall G p q T,
    inert G ->
    G ⊢!! p : T ->
    G ⊢!!! p : typ_sngl q ->
    exists q', typ_sngl q' = T /\ (q = q' \/ G ⊢!!! q' : typ_sngl q).
Proof.
  introv Hi Hp Hpq. gen T. dependent induction Hpq; introv Hp.
  - exists q. split*. apply* pt2_unique. apply* sngl_inert_sngl.
  - lets Hu: (pt2_unique Hi H Hp (sngl_inert_sngl q0)). subst*.
Qed.

Lemma pt3_invert : forall G p q T,
    inert G ->
    G ⊢!!! p : T ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! q: T \/ exists q', typ_sngl q' = T /\ (q = q' \/ G ⊢!!! q' : typ_sngl q).
Proof.
  introv Hi Hp Hpq. gen q. dependent induction Hp; introv Hpq.
  - right. apply* pt23_invert.
  - destruct (pt23_invert Hi H Hpq) as [q' [Heq [Heq' | Hq']]]; inversions Heq; eauto.
Qed.

Lemma inv_sngl_trans_helper: forall G p q T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢## p: T ->
    G ⊢## q: T \/ exists q', typ_sngl q' = T /\ (q = q' \/ G ⊢!!! q' : typ_sngl q).
Proof.
  introv Hi Hpq Hp. gen q. dependent induction Hp; introv Hpq.
  - destruct* (pt3_invert Hi H Hpq).
  - destruct (IHHp Hi _ Hpq); eauto.
    right. destruct_all; subst; inversion H0.
  - destruct (IHHp Hi _ Hpq); eauto.
    right. destruct_all; subst; inversion H1.
  - destruct (IHHp Hi _ Hpq); eauto.
    right. destruct_all; subst; inversion H1.
  - destruct (IHHp2 Hi _ Hpq); destruct (IHHp1 Hi _ Hpq).
    * left. eauto.
    * destruct H0 as [q' [Heq [Heq' | Hq']]]; subst.
      ** Abort.



Lemma repl_sngl_trans_helper: forall G p q T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢// p: T ->
             (exists r rt,
                 T = typ_sngl rt /\
                 G ⊢!!! q : typ_sngl r /\
                 G ⊢!!! rt : typ_sngl r)
             \/ G ⊢// q : T.
Proof. Abort.


Lemma repl_sngl_trans: forall G p q T,
    inert G ->
    G ⊢// p : typ_sngl q ->
    G ⊢// q : T ->
    G ⊢// p : T.
Proof.
  introv Hi Hpq Hq. gen T. dependent induction Hpq; introv Hq.
  + SCase "ty_inv_r".
    gen p. induction Hq; introv Hp; eauto.
    * constructor. apply* inv_sngl_trans.
    * specialize (IHHq Hi _ Hp). lets Hr: (repl_comp_open p p0 T).
      destruct (inv_to_precise_sngl_repl_comp Hp) as [r [Hpr Hc]].
      destruct (sngl_typed3 Hi Hpr) as [U Hru].
      destruct (repl_comp_to_prec Hi Hc Hru) as [Heq | Hrt]; clear Hru Hr U Hp.
      ** subst. clear Hc.
         lets Hr: (repl_comp_open p p0 T).
         lets Hrc: (replacement_repl_closure_qp_comp Hi IHHq Hpr Hr). eauto.
      ** lets Hr: (repl_comp_open p r T).
         lets Hrc: (replacement_repl_closure_qp_comp Hi IHHq Hrt Hr).
         lets Hr': (repl_comp_open r p0 T).
         lets Hrc': (replacement_repl_closure_qp_comp Hi Hrc Hpr Hr'). eauto.
  + SCase "ty_sngl_pq_inv".
    lets Hc: (replacement_repl_closure_qp Hi H Hpq H0).
    specialize (IHHpq _ Hi eq_refl).
    destruct (repl_prefixes_sngl H0) as [bs [He1 He2]]. subst.
    clear H0. destruct (repl_prec_exists Hq) as [U Hex].
    lets Htr: (pt3_trans_trans _ Hi (pt3 (pt2 H)) Hex).
    destruct (repl_sngl_trans_helper2 Hi Htr Hq) as [[q [rt [Heq [Hr1 Hr2]]]] | Hqt].
    * subst.
      assert (repl_typ n (q0 •• bs) q (typ_sngl (q0 •• bs)) (typ_sngl q)) as Hr by admit.
      lets Hrc: (replacement_repl_closure_pq3 Hi Hpq Hr1 Hr).
      assert (repl_typ n q rt (typ_sngl q) (typ_sngl rt)) as Hr' by admit.
      apply* replacement_repl_closure_qp3.
    * eauto.
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
