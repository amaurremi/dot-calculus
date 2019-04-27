(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Precise Typing (Elimination Typing II and III) *)

(** This module reasons about
    - properties of precise typing ⊢!! and ⊢!!! (only defined for paths)
    - about well-formedness of environments which is defined through precise typing
    - about equivalent types (path replacement with well-typed paths)
 *)

Set Implicit Arguments.

Require Import Sequences.
Require Import Coq.Program.Equality List.
Require Import Definitions Binding RecordAndInertTypes Replacement.
Require Export PreciseFlow.

Reserved Notation "G '⊢!!' p ':' T" (at level 40, p at level 59).
Reserved Notation "G '⊢!!!' p ':' T" (at level 40, p at level 59).

(** ** II-level Precise Typing *)
Inductive precise_typing2: ctx -> path -> typ -> Prop :=
| pt2: forall G p T U,
    G ⊢! p : T ⪼ U ->
    G ⊢!! p: U
| pt2_sngl_trans : forall G p q a U,
    G ⊢!! p : {{ q }} ->
    G ⊢!! q•a : U ->
    G ⊢!! p•a : {{ q•a }}
where "G '⊢!!' p ':' T" := (precise_typing2 G p T).

(** ** III-level Precise Typing *)
Inductive precise_typing3: ctx -> path -> typ -> Prop :=
| pt3: forall G p T,
    G ⊢!! p : T ->
    G ⊢!!! p: T
| pt3_sngl_trans : forall G p q T,
    G ⊢!! p : {{ q }} ->
    G ⊢!!! q : T ->
    G ⊢!!! p : T
where "G '⊢!!!' p ':' T" := (precise_typing3 G p T).

Hint Constructors precise_typing2 precise_typing3.

(** *** Properties of ⊢!! and ⊢!!!. Relationships between ⊢!, ⊢!!, and ⊢!!! *)

Lemma precise_to_general2: forall G p T,
    G ⊢!! p: T ->
    G ⊢ trm_path p : T.
Proof.
  introv Hp. induction Hp; eauto using precise_to_general.
Qed.

Lemma precise_to_general3: forall G p T,
    G ⊢!!! p: T ->
    G ⊢ trm_path p : T.
Proof.
  introv Hp. induction Hp; eauto using precise_to_general2.
Qed.

Lemma pt2_and_destruct1: forall G p T U,
    G ⊢!! p: T ∧ U ->
    G ⊢!! p: T.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

Lemma pt2_and_destruct2: forall G p T U,
    G ⊢!! p: T ∧ U ->
    G ⊢!! p: U.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

Lemma pt3_and_destruct1: forall G p T U,
    G ⊢!!! p: T ∧ U ->
    G ⊢!!! p: T.
Proof.
  introv Hp. dependent induction Hp; eauto. constructor.
  apply* pt2_and_destruct1.
Qed.

Lemma pt3_and_destruct2: forall G p T U,
    G ⊢!!! p: T ∧ U ->
    G ⊢!!! p: U.
Proof.
  introv Hp. dependent induction Hp; eauto. constructor.
  apply* pt2_and_destruct2.
Qed.

Lemma pt2_inertsngl : forall G p T,
    inert G ->
    G ⊢!! p: T ->
    inert_sngl T \/ record_type T.
Proof.
  introv Hi Pf. induction Pf.
  - apply* pf_inertsngl.
  - left. right. eexists. eauto.
Qed.

Lemma pt3_inertsngl : forall G p T,
    inert G ->
    G ⊢!!! p: T ->
    inert_sngl T \/ record_type T.
Proof.
  introv Hi Pf. induction Pf; eauto;
  apply* pt2_inertsngl.
Qed.

Lemma pt2_psel: forall G p q A,
    inert G ->
    G ⊢!! p : q ↓ A -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pf_psel.
Qed.

Lemma pt3_psel: forall G p q A,
    inert G ->
    G ⊢!!! p : q ↓ A -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pt2_psel.
Qed.

Lemma pt3_trans: forall G p q a U,
    G ⊢!! p : {{ q }}->
    G ⊢!!! q•a : U ->
    G ⊢!!! p•a : U.
Proof.
  introv Hp Hq. gen p. dependent induction Hq; introv Hp; eauto.
Qed.

Lemma pt3_trans2: forall G p q a U,
    G ⊢!!! p : {{ q }}->
    G ⊢!!! q•a : U ->
    G ⊢!!! p•a : U.
Proof.
  introv Hp Hq. gen a U. dependent induction Hp; introv Hq.
  - apply* pt3_trans.
  - specialize (IHHp _ eq_refl _ _ Hq). apply* pt3_trans.
Qed.

Lemma pt3_field_elim: forall G p a T,
    G ⊢!!! p : typ_rcd { a ⦂ T } ->
    G ⊢!!! p•a : T.
Proof.
  introv Hp. dependent induction Hp.
  - dependent induction H; eauto.
  - specialize (IHHp _ _ eq_refl).
    gen p. dependent induction IHHp; introv Hpq; eauto.
Qed.

Lemma path_elim_prec: forall G p q a T,
    inert G ->
    G ⊢!!! p: {{ q }}->
    G ⊢!!! q•a : T ->
    G ⊢!!! p•a : {{ q•a }}.
Proof.
  introv Hi Hp Hq.
  gen a T. dependent induction Hp; introv Hq.
  - inversion* Hq.
  - specialize (IHHp _ Hi eq_refl _ _ Hq). apply* pt3_trans.
Qed.

Lemma pf_pt2: forall G p T U V,
    inert G ->
    G ⊢! p: T ⪼ U ->
    G ⊢!! p: V ->
    inert_sngl V ->
    T = V.
Proof.
  introv Hi Hp1 Hp2 His. gen T U. induction Hp2; introv Hp1.
  - lets Heq: (pf_T_unique Hi Hp1 H). subst. destruct His.
    * destruct H0. apply* pf_forall_T. apply* pf_bnd_T.
    * inversions H0. destruct_all. apply* pf_sngl_T.
  - destruct (pf_path_sel _ _ Hi Hp1) as [V Hp].
    assert (inert_sngl {{ q }}) as His'. { right. eexists. auto. }
    specialize (IHHp2_1 Hi His' _ _ Hp). inversion IHHp2_1.
Qed.

Lemma pf_pt2_sngl: forall G p T U q,
    inert G ->
    G ⊢! p: T ⪼ U ->
    G ⊢!! p: {{ q }}->
    T = {{ q }}.
Proof.
  introv Hi Hp1 Hp2. apply* pf_pt2. right. eexists. auto.
Qed.

Lemma field_elim_q0: forall G p q a T,
    inert G ->
    G ⊢! p: {{ q }}⪼ {{ q }}->
    G ⊢!! p•a : T ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen q.
  dependent induction Hpa; introv Hp; eauto.
  - dependent induction H; try simpl_dot; eauto.
    lets Heq: (pf_T_unique Hi Hp H). subst.
    apply pf_sngl_U in H. inversion H.
  - clear IHHpa1 IHHpa2. simpl_dot.
    lets Heq: (pf_pt2_sngl Hi Hp Hpa1). inversion* Heq.
Qed.

Lemma field_elim_q0': forall G p q a T T',
    inert G ->
    G ⊢!! p: {{ q }}->
    G ⊢! p•a : T ⪼ T' ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen q.
  dependent induction Hpa; introv Hp; try simpl_dot; eauto.
  lets Hp2: (pf_pt2_sngl Hi Hpa Hp). subst.
  apply pf_sngl_U in Hpa. inversion Hpa.
Qed.

Lemma pf_pt2_sngl_invert G p q a T U :
    inert G ->
    G ⊢!! p: {{ q }}->
    G ⊢! p•a : T ⪼ U ->
    False.
Proof.
  intros Hi Hp Hpf.
  assert (exists V S, G ⊢! p: V ⪼ S) as [V [S Hpvs]]. {
      dependent induction Hpf; try simpl_dot; eauto.
    }
  lets ->: (pf_pt2_sngl Hi Hpvs Hp). clear Hp.
  dependent induction Hpf; try simpl_dot; eauto.
  lets Heq: (pf_T_unique Hi Hpvs Hpf). subst. apply pf_sngl_U in Hpf as[=].
Qed.

Lemma pt2_sngl_exists: forall G p q T,
    inert G ->
    G ⊢!! p: {{ q }}->
    G ⊢!! p: T ->
    exists q', T = {{ q' }}.
Proof.
  introv Hi Hp Ht. gen T. dependent induction Hp; introv Ht; eauto.
  - lets ->: (pf_sngl_T Hi H). dependent induction Ht; eauto.
    lets Heq: (pf_T_unique Hi H H0). subst. eauto using pf_sngl_U.
  - dependent induction Ht; eauto.
    lets Contra: (pf_pt2_sngl_invert _ Hi Hp1 H). inversion Contra.
Qed.

Lemma pt2_sngl_unique: forall G p q1 q2,
    inert G ->
    G ⊢!! p: {{ q1 }} ->
    G ⊢!! p: {{ q2 }} ->
    q1 = q2.
Proof.
  introv Hi Hp. gen q2. dependent induction Hp; introv Ht; eauto.
  - lets ->: (pf_sngl_T Hi H). dependent induction Ht; eauto.
    * lets Heq: (pf_T_unique Hi H H0). subst.
      apply pf_sngl_U in H0 as [=]. auto.
    * lets Contra: (pf_pt2_sngl_invert _ Hi Ht1 H). inversion Contra.
  - specialize (IHHp1 _ Hi eq_refl). gen q U.
    dependent induction Ht; introv Hpq IH1; introv Hqa IH2.
    * lets Contra: (pf_pt2_sngl_invert _ Hi Hpq H). inversion Contra.
    * simpl_dot. f_equal. eauto.
Qed.

Lemma pt2_sngl_unique' G p q T :
    inert G ->
    G ⊢!! p: {{ q }}->
    G ⊢!! p: T ->
    T = {{ q }}.
Proof.
  introv Hi Hp Hpt. destruct (pt2_sngl_exists Hi Hp Hpt) as [q' ->]. f_equal.
  eauto using pt2_sngl_unique.
Qed.

Lemma field_elim_q: forall G p q a T,
    inert G ->
    G ⊢!! p: {{ q }}->
    G ⊢!! p•a : T ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen a T. dependent induction Hp; introv Hpa.
  - lets Heq: (pf_sngl_T Hi H). subst. apply* field_elim_q0.
  - clear IHHp1 IHHp2.
    gen q0 U. dependent induction Hpa; introv Hp; introv Hq0.
    * apply* field_elim_q0'.
    * unfold sel_fields in x. destruct p0, p. inversions x.
      lets Hxbs: (pt2_sngl_trans _ Hp Hq0).
      assert (inert_sngl {{ q }}) as His. {
        right. eexists. eauto.
      }
      simpl in *.
      lets Hu: (pt2_sngl_unique Hi Hpa1 Hxbs).
      inversions Hu. eauto.
Qed.

Lemma field_elim_q2: forall G p q a T,
    inert G ->
    G ⊢!!! p: {{ q }}->
    G ⊢!! p•a : T ->
    exists U, G ⊢!!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen a T. dependent induction Hp; introv Hpa.
  - destruct* (field_elim_q _ Hi H Hpa).
  - specialize (IHHp _ Hi eq_refl).
    destruct (field_elim_q _ Hi H Hpa) as [V Hqa]. apply* IHHp.
Qed.

Lemma field_elim_q3: forall G p q a T,
    inert G ->
    G ⊢!!! p: {{ q }}->
    G ⊢!!! p•a : T ->
    exists U, G ⊢!!! q•a: U.
Proof.
  introv Hi Hp Hpa.
  gen q. dependent induction Hpa; introv Hp.
  - gen a T. dependent induction Hp; introv Hpa;
               destruct* (field_elim_q _ Hi H Hpa).
  - clear IHHpa Hpa T. gen a q. dependent induction Hp; introv Hpa.
    * destruct* (field_elim_q _ Hi H Hpa).
    * lets Hp': (pt3_sngl_trans H Hp). apply* field_elim_q2.
Qed.

Lemma pt3_field_elim_p: forall G p q a U,
    inert G ->
    G ⊢!!! p: {{ q }}->
    G ⊢!!! p • a : U ->
    G ⊢!!! p • a : {{ q•a }}.
Proof.
  introv Hi Hpq Hpa. destruct (field_elim_q3 _ Hi Hpq Hpa) as [T Hqa].
  apply* path_elim_prec.
Qed.

Lemma pt2_backtrack : forall G p a T,
    G ⊢!! p • a : T ->
    exists U, G ⊢!! p : U.
Proof.
  introv Hp. dependent induction Hp; eauto.
  - dependent induction H; try simpl_dot; eauto.
  - simpl_dot. eauto.
Qed.

Lemma pt3_backtrack : forall G p a T,
    G ⊢!!! p • a : T ->
    exists U, G ⊢!!! p : U.
Proof.
  introv Hp. dependent induction Hp;
               apply pt2_backtrack in H; destruct_all; eauto.
Qed.

Lemma pt3_sngl_trans3: forall G p q T,
    G ⊢!!! p: {{ q }}->
    G ⊢!!! q: T ->
    G ⊢!!! p : T.
Proof.
  introv Hp Hq. gen T. dependent induction Hp; introv Hq; eauto.
Qed.

Lemma pt3_field_trans: forall G p q bs T,
    inert G ->
    G ⊢!!! p : {{ q }}->
    G ⊢!!! q••bs : T ->
    G ⊢!!! p••bs : {{ q••bs }}.
Proof.
  introv Hi Hp Hq. gen T q. induction bs; introv Hp Hq;
                              unfolds sel_fields; destruct q, p; simpls; auto.
  rewrite proj_rewrite in *.
  destruct (pt3_backtrack _ _ Hq) as [U Hb].
  specialize (IHbs _ _ Hp Hb). rewrite proj_rewrite. apply* path_elim_prec.
Qed.

Lemma pt3_field_trans': forall G p q bs T,
    inert G ->
    G ⊢!!! p : {{ q }}->
    G ⊢!!! q••bs : T ->
    G ⊢!!! p••bs : T.
Proof.
  introv Hi Hp1 Hp2. gen p q T.
  induction bs; introv Hp1; introv Hp2; unfolds sel_fields; destruct q, p; simpls.
  - apply* pt3_sngl_trans3.
  - rewrite proj_rewrite in *.
    destruct (pt3_backtrack _ _ Hp2) as [S Hb].
    lets Hh: (pt3_field_trans _ Hi Hp1 Hb).
    apply* pt3_sngl_trans3. apply* path_elim_prec.
Qed.

Lemma pt2_weaken_one G p T x U :
  ok (G & x ~ U) ->
  G ⊢!! p : T ->
  G & x ~ U ⊢!! p : T.
Proof.
  intros Hx Hp. induction Hp.
  - econstructor. rewrite <- concat_empty_r in Hx. apply* pf_weaken_one. do 2 eapply ok_concat_inv_l; eauto.
  - eapply pt2_sngl_trans; eauto.
Qed.

Lemma pt2_weaken G p T G' :
  ok (G & G') ->
  G ⊢!! p : T ->
  G & G' ⊢!! p : T.
Proof.
  intros Hok Hp. induction G' using env_ind.
  - rewrite* concat_empty_r.
  - rewrite concat_assoc in *. apply* pt2_weaken_one.
Qed.

Lemma pt3_weaken_one G p T x U :
  ok (G & x ~ U) ->
  G ⊢!!! p : T ->
  G & x ~ U ⊢!!! p : T.
Proof.
  intros Hx Hp. induction Hp.
  - econstructor. rewrite <- concat_empty_r in Hx. apply* pt2_weaken_one.
  - eapply pt3_sngl_trans; eauto. apply* pt2_weaken_one.
Qed.

Lemma pt3_weaken G G' p T :
  ok (G & G') ->
  G ⊢!!! p: T ->
  G & G' ⊢!!! p: T.
Proof.
  intros Hok Hp. induction G' using env_ind.
  - rewrite* concat_empty_r.
  - rewrite concat_assoc in *. apply* pt3_weaken_one.
Qed.

Lemma pf_strengthen_full G p T U :
  inert G ->
  G ⊢! p : T ⪼ U ->
  exists G1 G2 x bs V, G = G1 & x ~ V & G2 /\
                p = p_sel (avar_f x) bs /\
                G1 & x ~ V ⊢! p : T ⪼ U.
Proof.
  intros Hi Hp.
  pose proof (typed_paths_named (precise_to_general Hp)) as [x [bs ->]].
  induction G as [|G1 y V] using env_ind.
  - apply precise_to_general in Hp. false* typing_empty_false.
  - destruct (classicT (y = x)) as [-> | Hn].
    + repeat eexists; eauto. rewrite* concat_empty_r.
    + apply pf_strengthen in Hp; auto.
      specialize (IHG (inert_prefix Hi) Hp) as [G1' [G2' [z [cs [W [-> [[= -> ->] Hp']]]]]]].
      repeat eexists; eauto. rewrite concat_assoc. eauto.
Qed.

Lemma pt2_destruct_env G p T :
  inert G ->
  G ⊢!! p : T ->
  exists G1 G2 x bs V, G = G1 & x ~ V & G2 /\
                  p = p_sel (avar_f x) bs.
Proof.
  intros Hi Hp. induction Hp.
  - apply pf_strengthen_full in H; auto. destruct_all; repeat eexists; eauto.
  - specialize (IHHp1 Hi). specialize (IHHp2 Hi). destruct_all. simpl_dot. repeat eexists.
Qed.

Lemma pt2_var_sngl G x p :
  inert G ->
  G ⊢!! pvar x : {{ p }}->
  False.
Proof.
  intros Hi Hp. dependent induction Hp; try simpl_dot.
  pose proof (pf_sngl_T Hi H) as ->. apply (pf_binds Hi) in H.
  apply (binds_inert H) in Hi. inversion Hi.
Qed.

Lemma pt2_to_pf G p T :
  G ⊢!! p : T ->
  (inert_typ T \/ record_type T) ->
  exists U, G ⊢! p : U ⪼ T.
Proof.
  intros Hp [Hin | Hr].
  - inversions Hin; inversions Hp; eauto.
  - inversions Hr. inversions H; inversions Hp; eauto.
Qed.

Lemma pt3_trans_trans: forall G p q bs T,
    inert G ->
    G ⊢!!! p : {{ q }}->
    G ⊢!!! p••bs : T ->
    G ⊢!!! p••bs : {{ q••bs }}.
Proof.
  introv Hi Hp Hpbs. gen p q T.
  induction bs; introv Hp; introv Hpbs; unfolds sel_fields; destruct p, q; simpls; auto.
  repeat rewrite proj_rewrite in *. apply* pt3_field_elim_p.
  specialize (IHbs _ _ Hp). apply pt3_backtrack in Hpbs. destruct_all. eauto.
Qed.

Lemma pf_sngl_fld_elim: forall G p q a T U,
    inert G ->
    G ⊢! p: {{ q }}⪼ {{ q }}->
    G ⊢! p•a : T ⪼ U ->
    False.
Proof.
  introv Hi Hp Hpa. dependent induction Hpa; try simpl_dot; eauto.
  lets Hu: (pf_T_unique Hi Hpa Hp). subst. apply pf_sngl_U in Hpa. false*.
Qed.

Lemma pf_sngl_flds_elim: forall G p q T U bs,
    inert G ->
    G ⊢! p: {{ q }}⪼ {{ q }}->
    G ⊢! p••bs : T ⪼ U ->
    bs = nil.
Proof.
  introv Hi Hp Hpbs. gen T U. induction bs; introv Hpbs. auto.
  assert (exists T' U', G ⊢! p •• bs : T' ⪼ U') as [T' [U' Hpbs']]. {
    clear IHbs Hp. dependent induction Hpbs; try simpl_dot; eauto.
    unfolds sel_field, sel_fields. destruct p0, p. inversions x. repeat eexists. eauto.
  }
  specialize (IHbs _ _ Hpbs'). subst. unfold sel_fields in Hpbs. destruct p. simpls.
  rewrite proj_rewrite in *. false* pf_sngl_fld_elim.
Qed.

Lemma pt2_bnd : forall G p T,
    inert G ->
    G ⊢!! p: μ T ->
    G ⊢!! p: open_typ_p p T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
Qed.

Lemma pt2_exists: forall G p T,
    G ⊢!!! p: T ->
    exists U, G ⊢!! p: U.
Proof.
  induction 1; eauto.
Qed.

Lemma pt3_bnd : forall G p T,
    inert G ->
    G ⊢!!! p: μ T ->
    G ⊢!!! p: open_typ_p p T \/
              (exists q U, G ⊢!!! p: {{ q }}/\ G ⊢!! q : U /\ G ⊢!!! p: open_typ_p q T).
Proof.
  introv Hi Hp. dependent induction Hp.
  - left. constructor. apply* pt2_bnd.
  - specialize (IHHp _ Hi eq_refl). destruct IHHp as [Hq | [r [U [Hr1 [Hq Hr2]]]]]; right.
    + apply pt2_exists in Hp as [? ?]. repeat eexists; eauto.
    + exists r. repeat eexists; eauto.
Qed.

Lemma pf_pt2_trans_inv_mult : forall G p q bs T,
    inert G ->
    G ⊢! p: {{ q }}⪼ {{ q }}->
    G ⊢!! p •• bs : T ->
    T = {{ q••bs }}.
Proof.
  introv Hi Hp Hpbs. gen T. induction bs; introv Hpbs.
  - repeat rewrite field_sel_nil in *. apply pt2 in Hp. apply eq_sym. apply eq_sym.
    eauto using pt2_sngl_unique'.
  - rewrite proj_rewrite' in *. destruct (pt2_backtrack _ _ Hpbs) as [U Hb].
    apply pt2 in Hp. specialize (IHbs _ Hb). subst.
    destruct (field_elim_q _ Hi Hb Hpbs) as [U Hf].
    lets Hp2: (pt2_sngl_trans _ Hb Hf).
    eauto using pt2_sngl_unique'.
Qed.

Lemma pf_pt3_trans_inv_mult : forall G p q T,
    inert G ->
    G ⊢!! p: {{ q }}->
    G ⊢!!! p : T ->
    inert_typ T \/ record_type T ->
    G ⊢!!! q : T.
Proof.
  introv Hi Hpq Hp Hr. gen q. induction Hp; introv Hpq.
  - constructor.
    assert (inert_sngl {{ q }}) as His. {
      right. eexists. eauto.
    }
    lets ->: (pt2_sngl_unique' Hi Hpq H). destruct Hr.
    inversion His. inversion H1. inversion H0. inversion H0. inversion H1.
  - specialize (IHHp Hi Hr).
    assert (inert_sngl {{ q }}) as His1. {
      right. eexists. eauto.
    }
    assert (inert_sngl {{ q0 }}) as His2. {
      right. eexists. eauto.
    }
    lets Heq: (pt2_sngl_unique' Hi Hpq H). inversions Heq. eauto.
Qed.

Lemma pf_pt3_trans_inv_mult' : forall G p q T bs,
    inert G ->
    G ⊢! p: {{ q }}⪼ {{ q }}->
    G ⊢!!! p •• bs : T ->
    inert_typ T \/ record_type T ->
    G ⊢!!! q •• bs : T.
Proof.
  introv Hi Hp Hpbs Hr.
  assert (exists U, G ⊢!! p •• bs : U) as [U Hu] by apply* pt2_exists.
  apply* pf_pt3_trans_inv_mult. lets Hpf: (pf_pt2_trans_inv_mult _ Hi Hp Hu). subst*.
Qed.

Lemma pf_pt3_unique : forall G p S A T U,
    inert G ->
    G ⊢! p: S ⪼ typ_rcd {A >: T <: T} ->
    G ⊢!!! p: typ_rcd {A >: U <: U} ->
    T = U.
Proof.
  introv Hi Hp1 Hp3. dependent induction Hp3.
  - apply pt2 in Hp1. dependent induction H. dependent induction Hp1.
    lets Hu: (pf_T_unique Hi H0 H). subst.
    destruct (pf_bnd_T2 Hi H0) as [V Heq]. subst.
    apply* pf_dec_typ_unique.
  - clear IHHp3. apply pt2 in Hp1. assert (inert_sngl {{ q }}) as His. {
      right. eexists. eauto.
    }
    lets Hu: (pt2_sngl_unique' Hi H Hp1). inversion Hu.
Qed.

Lemma pt23_invert : forall G p q T,
    inert G ->
    G ⊢!! p : T ->
    G ⊢!!! p : {{ q }}->
    exists q', {{ q' }} = T /\ (q = q' \/ G ⊢!!! q' : {{ q }}).
Proof.
  introv Hi Hp Hpq. gen T. dependent induction Hpq; introv Hp.
  - exists q. split*.
    apply eq_sym. apply* pt2_sngl_unique'.
  - lets Hu: (pt2_sngl_unique' Hi H Hp). subst*.
Qed.

Lemma pt3_invert : forall G p q T,
    inert G ->
    G ⊢!!! p : T ->
    G ⊢!!! p : {{ q }}->
    G ⊢!!! q: T \/ exists q', {{ q' }} = T /\ (q = q' \/ G ⊢!!! q' : {{ q }}).
Proof.
  introv Hi Hp Hpq. gen q. dependent induction Hp; introv Hpq.
  - right. apply* pt23_invert.
  - destruct (pt23_invert Hi H Hpq) as [q' [Heq [Heq' | Hq']]]; inversions Heq; eauto.
Qed.

Lemma pt3_var_sngl G x p :
  inert G ->
  G ⊢!!! pvar x : {{ p }}->
  False.
Proof.
  intros Hi Hp. dependent induction Hp; false* pt2_var_sngl.
Qed.

Lemma pf_inert_pt2_sngl_false G p q T U :
  inert G ->
  G ⊢! p : T ⪼ U ->
  G ⊢!! p : {{ q }}->
  inert_typ T ->
  False.
Proof.
  intros Hi Hp Hq Hin. gen q. dependent induction Hp; eauto; introv Hpq.
  - false* pt3_var_sngl.
  - lets Hp': (pf_fld Hp). pose proof (pf_pt2_sngl Hi Hp' Hpq) as ->. inversion Hin.
Qed.

Lemma pf_inert_pt3_sngl_false G p q T U :
  inert G ->
  G ⊢! p : T ⪼ U ->
  G ⊢!!! p : {{ q }}->
  inert_typ T ->
  False.
Proof.
  intros Hi Hp Hq Hin. gen T U. dependent induction Hq; introv Hin; introv Hp;
  apply* pf_inert_pt2_sngl_false.
Qed.

Lemma pt3_inert_pt2_sngl_invert G p q T :
  inert G ->
  G ⊢!!! p : T ->
  G ⊢!! p : {{ q }}->
  inert_typ T ->
  G ⊢!!! q : T.
Proof.
  intros Hi Hp Hpq Hin. gen q. induction Hp; introv Hpq.
  - pose proof (pt2_sngl_unique' Hi Hpq H) as ->. inversion Hin.
  - pose proof (pt2_sngl_unique Hi H Hpq) as ->. eauto.
Qed.

Lemma pt3_inert_sngl_invert G p q T :
  inert G ->
  G ⊢!!! p : T ->
  G ⊢!!! p : {{ q }}->
  inert_typ T ->
  G ⊢!!! q : T.
Proof.
  introv Hi Hp Hpq. gen T. dependent induction Hpq; introv Hp Hin;
                             [.. | apply* IHHpq];
                             eapply (pt3_inert_pt2_sngl_invert Hi Hp); eauto.
Qed.

Lemma pt2_dec_typ_tight: forall G p A S U,
    inert G ->
    G ⊢!! p: typ_rcd {A >: S <: U} ->
    S = U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pf_dec_typ_tight.
Qed.

Lemma pt3_dec_typ_tight: forall G p A S U,
    inert G ->
    G ⊢!!! p: typ_rcd {A >: S <: U} ->
    S = U.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pt2_dec_typ_tight.
Qed.

Lemma last_path G p T U :
  inert G ->
  G ⊢!!! p : ∀(T) U ->
  G ⊢!! p : ∀(T) U \/ exists q, G ⊢!!! p: {{ q }} /\ G ⊢!! q : ∀(T) U.
Proof.
  intros Hi Hp. dependent induction Hp; eauto.
  specialize (IHHp _ _ Hi eq_refl) as [Hq | [r [Hq Hr]]]; eauto.
Qed.

Lemma pt2_qbs_typed G p q T bs V:
  inert G ->
  G ⊢! p : {{ q }} ⪼ {{ q }} ->
  G ⊢!! q : T ->
  G ⊢!! p••bs : V ->
  exists U, G ⊢!! q •• bs : U.
Proof.
  intros Hi Hp Hq Hpbs.
  pose proof (pf_pt2_trans_inv_mult _ Hi Hp Hpbs) as ->.
  gen T. dependent induction Hpbs.
  - pose proof (pf_sngl_flds_elim _ Hi Hp H) as ->. rewrite* field_sel_nil.
  - destruct p0 as [p0x p0bs].
    destruct p as [px pbs].
    destruct q as [qx qbs].
    destruct q0 as [q0x q0bs]. inversions x0. inversions x. simpl in IHHpbs2, IHHpbs1.
    destruct bs as [|b bs].
    + rewrite app_nil_l in *. subst. eauto.
    + rewrite <- app_comm_cons in *. inversions H1. inversions H2. eauto.
Qed.

(** ** Wellformed paths and environments *)

Inductive wf : ctx -> Prop :=
| wfe_empty :
    wf empty
| wfe_push G x T :
    wf G ->
    x # G ->
    (forall bs q, G & x ~ T ⊢! p_sel (avar_f x) bs : {{ q }}⪼ {{ q }}->
             exists U, G & x ~ T ⊢!! q : U) ->
    wf (G & x ~ T).

Hint Constructors wf.

Lemma wf_prefix_one G x T :
  wf (G & x ~ T) -> wf G.
Proof.
  intros Hwf. dependent induction Hwf.
  - false* empty_push_inv.
  - apply eq_push_inv in x as [-> [-> ->]]. destruct G as [|G x U] using env_ind; auto.
Qed.

Lemma wf_prefix G G' :
  wf (G & G') -> wf G.
Proof.
  intros Hwf. gen G. induction G' using env_ind; introv Hwf.
  - rewrite concat_empty_r in Hwf; auto.
  - rewrite concat_assoc in *. apply IHG'. apply* wf_prefix_one.
Qed.

Hint Resolve wf_prefix wf_prefix_one.

(** ** Strengthening and Typing of Singleton Types *)
(** Strengthening is the opposite of weakening: removing elements
    of the typing environment. The strengthening lemmas state that
    in a well-formed environment [Γ, x: T], precise typing of a path [y.bs] is
 preserved in the strengthened environment [Γ] if [x ≠ y]. *)

Lemma pf_strengthen_one_helper G y bs T x q :
  inert (G & x ~ T) ->
  wf G ->
  G & x ~ T ⊢! p_sel (avar_f y) bs : {{ q }}⪼ {{ q }}->
  x <> y ->
  exists U, G ⊢!! q : U.
Proof.
  intros Hi Hwf. gen y bs q x T. dependent induction Hwf; introv Hi Hy Hn.
  - rewrite concat_empty_l in *. apply precise_to_general in Hy.
    apply typing_implies_bound in Hy as [S Hb]. apply binds_single_inv in Hb as [-> _]. false*.
  - apply pf_strengthen in Hy; auto.
    destruct (classicT (x = y)) as [-> | Hn']; eauto.
    specialize (IHHwf _ _ _ _ _ (inert_prefix Hi) Hy Hn') as [S Hq]. eexists. apply* pt2_weaken. apply inert_ok.
    apply inert_prefix in Hi; auto.
Qed.

Lemma pt2_strengthen_one_helper G y bs T x q :
  inert (G & x ~ T) ->
  wf G ->
  G & x ~ T ⊢!! p_sel (avar_f y) bs : {{ q }}->
  x <> y ->
  G ⊢!! p_sel (avar_f y) bs : {{ q }}/\ exists S, G ⊢!! q : S.
Proof.
  intros Hi Hwf Ht Hn. dependent induction Ht.
  - split. econstructor. apply* pf_strengthen.
    apply* pf_strengthen_one_helper. pose proof (pf_sngl_T Hi H) as ->. apply H.
  - simpl_dot.
    specialize (IHHt1 _ _ _ _ _ _ Hi Hwf JMeq_refl eq_refl eq_refl Hn) as [IHy [S IHq]].
    pose proof (typed_paths_named (precise_to_general2 Ht2)) as [qx [qbs Heq]]. simpl_dot. simpl in IHHt2.
    assert (x0 <> qx) as Hn'. {
      pose proof (typing_implies_bound (precise_to_general2 IHq)) as [W Hb].
      apply inert_ok in Hi. intros ->. apply ok_push_inv in Hi as [_ Hq]. eapply binds_fresh_inv; eauto.
    }
    rewrite proj_rewrite in *.
    pose proof (pt2_inertsngl Hi Ht2) as [[Hin | [q ->]] | Hr].
    + pose proof (pt2_to_pf Ht2 (or_introl Hin)) as [? Hpr]. apply pf_strengthen in Hpr; auto; split*.
    + specialize (IHHt2 _ _ _ _ _ _ Hi Hwf JMeq_refl eq_refl eq_refl Hn') as [IHqx [W IHq']].
      split.
      * rewrite proj_rewrite in *. eauto.
      * simpl. eexists; eauto.
    + pose proof (pt2_to_pf Ht2 (or_intror Hr)) as [? Hpr]. apply pf_strengthen in Hpr; auto; split*.
Qed.

Lemma pt2_strengthen_one G y bs T x U :
  inert (G & x ~ T) ->
  wf G ->
  G & x ~ T ⊢!! p_sel (avar_f y) bs : U ->
  x <> y ->
  G ⊢!! p_sel (avar_f y) bs : U.
Proof.
  intros Hi Hwf Ht Hn.
  pose proof (pt2_inertsngl Hi Ht) as [[Hin | [q ->]] | Hr].
  - pose proof (pt2_to_pf Ht (or_introl Hin)) as [? Hpr]. apply pf_strengthen in Hpr; eauto.
  - apply* pt2_strengthen_one_helper.
  - pose proof (pt2_to_pf Ht (or_intror Hr)) as [? Hpr]. apply pf_strengthen in Hpr; eauto.
Qed.

(** *** Typing of paths that form singleton types *)

(** The following lemmas state that if a path has a precise type [q.type]
    in a well-formed environment, then [q] is typeable. *)

Lemma sngl_typed G p q :
    inert G ->
    wf G ->
    G ⊢! p: {{ q }}⪼ {{ q }}->
    exists T, G ⊢!! q: T.
Proof.
  intros Hi Hwf Hp. gen p q.
  induction Hwf; introv Hpq.
  - apply precise_to_general in Hpq. false* typing_empty_false.
  - pose proof (typed_paths_named (precise_to_general Hpq)) as [px [pbs ->]].
    destruct (classicT (x = px)) as [-> | Hn]; eauto.
    pose proof (pf_strengthen_one_helper Hi Hwf Hpq Hn) as [U Hq]. eexists. apply* pt2_weaken.
Qed.

Lemma sngl_typed2 : forall G p q,
    inert G ->
    wf G ->
    G ⊢!! p: {{ q }}->
    exists T, G ⊢!! q: T.
Proof.
  introv Hi Hwf Hpq. dependent induction Hpq; eauto.
  pose proof (pf_sngl_T Hi H) as ->. apply* sngl_typed.
Qed.

Lemma sngl_typed3 : forall G p q,
    inert G ->
    wf G ->
    G ⊢!!! p: {{ q }}->
    exists T, G ⊢!!! q: T.
Proof.
  introv Hi Hwf Hp. dependent induction Hp; eauto.
  destruct* (sngl_typed2 Hi Hwf H).
Qed.

Lemma pt2_fld_strengthen G p a T U G' :
  inert (G & G') ->
  wf G ->
  G ⊢!! p : T ->
  G & G' ⊢!! p • a : U ->
  G ⊢!! p • a : U.
Proof.
  intros Hi Hwf Hp Hpa. gen T. dependent induction Hpa; introv Hp.
  - pose proof (pf_strengthen_full Hi H) as [G1 [G2 [px [pbs [V [HeqG [Heqp Hp1]]]]]]]. simpl_dot.
    pose proof (pt2_destruct_env (inert_prefix Hi) Hp) as [G1' [G2' [px' [pbs' [V' [-> [= -> ->]]]]]]].
    rewrite <- concat_assoc in *. apply env_ok_inv' in HeqG as [-> [-> <-]].
    + rewrite concat_assoc in *. apply* pt2_weaken. apply* inert_ok. apply* inert_prefix.
    + apply* inert_ok.
  - simpl_dot.
    destruct f0.
    + pose proof (typed_paths_named (precise_to_general2 Hpa1)) as [px [pbs [= -> <-]]]. false* pt2_var_sngl.
    + rewrite proj_rewrite in *.
      pose proof (pt2_backtrack _ _ Hp) as [W Hpb]. specialize (IHHpa1 _ _ _ _ Hi Hwf JMeq_refl eq_refl _ Hpb).
      specialize (IHHpa2 _ _ _ _ Hi Hwf JMeq_refl eq_refl).
      pose proof (sngl_typed2 (inert_prefix Hi) Hwf IHHpa1) as [X Hq]. eauto.
Qed.

Lemma pt2_strengthen G G1 G2 bs T x U :
  G = G1 & x ~ T & G2 ->
  inert G ->
  wf G ->
  G ⊢!! p_sel (avar_f x) bs : U ->
  G1 & x ~ T ⊢!! p_sel (avar_f x) bs : U.
Proof.
  intros -> Hi Hwf Hp. induction G2 using env_ind.
  - rewrite concat_empty_r in *. auto.
  - destruct (classicT (x0 = x)) as [-> | Hn].
    + apply inert_ok in Hi. apply ok_middle_inv_r in Hi. simpl_dom. apply notin_union in Hi as [Contra _].
      false* notin_same.
    + rewrite concat_assoc in *. eapply pt2_strengthen_one in Hp; auto.
      specialize (IHG2 (inert_prefix Hi) (wf_prefix Hwf) Hp). eauto. apply* wf_prefix.
Qed.

Lemma pt3_strengthen_one G bs T x y U :
  inert (G & x ~ T) ->
  wf (G & x ~ T) ->
  G & x ~ T ⊢!!! p_sel (avar_f y) bs : U ->
  y <> x ->
  G ⊢!!! p_sel (avar_f y) bs : U.
Proof.
  intros Hi Hwf Hp Hn. dependent induction Hp.
  - constructor. apply* pt2_strengthen_one.
  - pose proof (sngl_typed2 Hi Hwf H) as [U Ht%precise_to_general2]. apply typed_paths_named in Ht as [qx [qbs ->]].
    destruct (classicT (qx = x)) as [-> | Hn'].
    + clear IHHp. apply pt2_strengthen_one in H; eauto.
      apply (sngl_typed2 (inert_prefix Hi)) in H as [S Ht]; eauto.
      apply (pt2_destruct_env (inert_prefix Hi)) in Ht as [G1 [G2 [px [pbs [V [-> [= -> ->]]]]]]].
      apply inert_ok in Hi. rewrite <- concat_assoc in Hi. apply ok_middle_inv_r in Hi.
      simpl_dom. apply notin_union in Hi as [Contra _]. false* notin_same.
    + apply pt2_strengthen_one in H; eauto.
Qed.

Lemma pt3_strengthen G G1 G2 bs T x U :
  G = G1 & x ~ T & G2 ->
  inert G ->
  wf G ->
  G ⊢!!! p_sel (avar_f x) bs : U ->
  G1 & x ~ T ⊢!!! p_sel (avar_f x) bs : U.
Proof.
  intros -> Hi Hwf Hp. induction G2 using env_ind.
  - rewrite concat_empty_r in *. auto.
  - destruct (classicT (x0 = x)) as [-> | Hn].
    + apply inert_ok in Hi. apply ok_middle_inv_r in Hi. simpl_dom. apply notin_union in Hi as [Contra _].
      false* notin_same.
    + rewrite concat_assoc in *. apply pt3_strengthen_one in Hp; auto.
      specialize (IHG2 (inert_prefix Hi) (wf_prefix Hwf) Hp). eauto.
Qed.

Lemma pt2_strengthen_full G p T :
  inert G ->
  wf G ->
  G ⊢!! p : T ->
  exists G1 G2 x bs V, G = G1 & x ~ V & G2 /\
                  p = p_sel (avar_f x) bs /\
                  G1 & x ~ V ⊢!! p : T.
Proof.
  intros Hi Hwf Hp. pose proof (pt2_destruct_env Hi Hp) as [G1 [G2 [x [bs [V [-> ->]]]]]].
  repeat eexists. apply* pt2_strengthen.
Qed.

Lemma pt2_strengthen_from_pf G G' p bs T T' U :
  inert (G & G') ->
  wf (G & G') ->
  G ⊢! p: T ⪼ T' ->
  G & G' ⊢!! p••bs : U ->
  G  ⊢!! p••bs : U.
Proof.
  intros Hi Hwf Hp1 Hp2. gen U. induction bs; introv Hp2.
  - rewrite field_sel_nil in *.
    apply pt2_strengthen_full in Hp2 as [G1 [G2 [px [pbs [V [Heq [-> Ht]]]]]]]; auto.
    pose proof (pt2_destruct_env (inert_prefix Hi) (pt2 Hp1)) as [G1' [G2' [px' [pbs' [V' [-> [= -> ->]]]]]]].
    rewrite <- concat_assoc in *. pose proof (inert_ok Hi) as Hok.
    apply env_ok_inv' in Heq as [-> [-> <-]]; rewrite concat_assoc in *; auto.
    apply* pt2_weaken.
  - rewrite proj_rewrite' in *. pose proof (pt2_backtrack _ _ Hp2) as [V Hb].
    specialize (IHbs _ Hb).
    pose proof (pt2_fld_strengthen _ Hi (wf_prefix Hwf) IHbs Hp2). eauto.
Qed.

Lemma pt3_strengthen_full G p T :
  inert G ->
  wf G ->
  G ⊢!!! p : T ->
  exists G1 G2 x bs V, G = G1 & x ~ V & G2 /\
                  p = p_sel (avar_f x) bs /\
                  G1 & x ~ V ⊢!!! p : T.
Proof.
  intros Hi Hwf Hp. induction Hp.
  - pose proof (pt2_destruct_env Hi H) as [G1 [G2 [x [bs [V [-> ->]]]]]].
    repeat eexists. constructor. apply* pt2_strengthen.
  - specialize (IHHp Hi Hwf) as [G1 [G2 [x [bs [V [-> [-> Hp3]]]]]]].
    pose proof (pt2_strengthen_full Hi Hwf H) as [G1' [G2' [y [cs [W3 [Heq [-> Hp2]]]]]]].
    do 5 eexists. split. apply Heq. split*.
    assert (inert (G1' & y ~ W3)) as Hi' by (rewrite Heq in Hi; apply* inert_prefix).
    assert (wf (G1' & y ~ W3)) as Hwf'.
    { rewrite Heq in Hwf. eapply wf_prefix. eauto. }
    pose proof (sngl_typed2 Hi' Hwf' Hp2) as [U Hx].
    apply (pt2_strengthen_full Hi') in Hx as [G1'' [G2'' [z [ds [X [HeqG [[= <- <-] Hx]]]]]]].
    rewrite HeqG in Heq. do 2 rewrite <- concat_assoc in Heq. rewrite concat_assoc in Heq.
    apply env_ok_inv in Heq as [-> [-> ->]].
    apply pt2_weaken with (G':=G2'') in Hx. rewrite <- HeqG in Hx. eapply pt3_sngl_trans.
    apply Hp2. rewrite HeqG. apply* pt3_weaken. rewrite concat_assoc in Hi. apply inert_ok. apply* inert_prefix.
    rewrite concat_assoc in Hi. apply inert_ok. apply* inert_prefix.
    rewrite Heq in Hi. apply* inert_ok. auto.
Qed.

Lemma pt3_fld_strengthen G p a T U G' :
  inert (G & G') ->
  wf (G & G') ->
  G ⊢!!! p : T ->
  G & G' ⊢!!! p • a : U ->
  G ⊢!!! p • a : U.
Proof.
  intros Hi Hwf Hp Hpa.
  pose proof (pt3_strengthen_full Hi Hwf Hpa) as [G1 [G2 [px [pbs [V [HeqG [Heqp Hp1]]]]]]]. simpl_dot.
  pose proof (pt3_strengthen_full (inert_prefix Hi) (wf_prefix Hwf) Hp)
    as [G1' [G2' [px' [pbs' [V' [-> [[= <- <-] HHH]]]]]]].
  rewrite <- concat_assoc in *. apply env_ok_inv' in HeqG as [-> [-> <-]]; auto.
  rewrite concat_assoc in *. apply* pt3_weaken. apply inert_ok. apply* inert_prefix.
Qed.

Lemma pf_strengthen_from_pt3 G G' p T U V :
  inert (G & G') ->
  wf (G & G') ->
  G ⊢!!! p: T ->
  G & G' ⊢! p : U ⪼ V ->
  G  ⊢! p : U ⪼ V.
Proof.
  intros Hi Hwf Hp3 Hpf.
  apply (pf_strengthen_full Hi) in Hpf as [G1 [G2 [px [pbs [W [Heq [-> Hpf]]]]]]].
  apply (pt3_strengthen_full (inert_prefix Hi)) in Hp3 as [G1' [G2' [? [? [? [-> [[= <- <-] Hp3]]]]]]].
  rewrite <- concat_assoc in Heq. apply env_ok_inv in Heq as [-> [-> <-]].
  apply* pf_weaken. apply inert_ok. apply* inert_prefix. rewrite concat_assoc in Heq.
  rewrite Heq in Hi. auto. apply* wf_prefix.
Qed.

(** ** Replacement Composition *)

(** The [typed_repl_comp_qp] relation for equivalent types under a given environment
    states that for two types [T] and [U], [T[q/p,n]=U], where [p] and [q] are typed
    the environment. *)
Definition typed_repl_comp_qp G T1 T2 :=
  exists p q n U,
    G ⊢! p: {{ q }}⪼ {{ q }}/\
    G ⊢!! q : U /\
    repl_typ n q p T1 T2.

(** Reflexivte, transitive closure of [typed_repl_comp_qp]. [repl_composition_qp] allows
    us to express that types are equivalent as a result of multiple replacements *)
Definition repl_composition_qp G := star (typed_repl_comp_qp G).

Notation "G '⊢' T '⟿' U" := (repl_composition_qp G U T) (at level 40, T at level 59).
Notation "G '⊢' p '⟿'' q" := (G ⊢ {{ p }}⟿ {{ q }}) (at level 40, p at level 59).

(** In a well-formed environment, there is a precise-typing relation between equivalent
    singleton paths *)
Lemma repl_comp_to_prec': forall G G' p q T,
    inert (G & G') ->
    wf (G & G') ->
    G ⊢ p ⟿' q ->
    G & G' ⊢!!! p: T ->
    p = q \/ G ⊢!!! p: {{ q }}.
Proof.
  introv Hi Hwf Hr Hp. gen T. dependent induction Hr; introv Hp; eauto.
  assert (exists r, b = {{ r }}) as [r Heq].
  { inversion H as [? [? [? [? [_ [? Hr']]]]]]. inversion* Hr'. }
  subst.
  specialize (IHHr _ _ Hi Hwf eq_refl eq_refl). destruct (IHHr _ Hp). subst.
  - destruct H as [p1 [p2 [n [S [H1 [Hq H2]]]]]]. right. inversions H2.
    destruct (pt2_exists Hp) as [U Hu].
    apply (pt2_strengthen_from_pf _ Hi Hwf H1) in Hu.
    lets Hpf: (pf_pt2_trans_inv_mult _ (inert_prefix Hi) H1 Hu). subst*.
  - specialize (IHHr _ Hp). destruct H as [p1 [p2 [n [S [H1 [Hq H2]]]]]].
    destruct (repl_prefixes_sngl H2) as [bs [He1 He2]]. subst.
    destruct IHHr as [Heq | IH].
    * subst. right. lets Hs: (sngl_typed3 (inert_prefix Hi) (wf_prefix Hwf) (pt3 (pt2 H1))). destruct Hs.
      apply* pt3_trans_trans. apply* inert_prefix.
    * right*. apply* pt3_sngl_trans3.
      lets Hs: (sngl_typed3 (inert_prefix Hi) (wf_prefix Hwf) IH). destruct Hs.
      apply* pt3_trans_trans. apply* inert_prefix.
Qed.

(** The following lemmas reasoning about further properties of equivalent types. *)

Lemma repl_comp_sngl_inv1 : forall G T p,
    G ⊢ {{ p }} ⟿ T ->
    exists q, T = {{ q }}.
Proof.
  introv Hr. dependent induction Hr; eauto.
  specialize (IHHr _ eq_refl). destruct_all. subst.
  inversions H. destruct_all. invert_repl. eexists; eauto.
Qed.

Lemma repl_comp_sngl_inv2 : forall G T p,
    G ⊢ T ⟿ {{ p }}->
    exists q, T = {{ q }}.
Proof.
  introv Hr. dependent induction Hr; eauto.
  inversions H. destruct_all. invert_repl.
  specialize (IHHr _ eq_refl). destruct_all. eexists. eauto.
Qed.

Lemma repl_comp_bnd_inv1 G T U :
  G ⊢ μ U ⟿ T ->
  exists S, T = μ S.
Proof.
  introv Hr. dependent induction Hr; eauto.
  specialize (IHHr _ eq_refl). destruct_all. subst.
  inversions H. destruct_all. invert_repl. eexists; eauto.
Qed.

Lemma repl_comp_bnd_inv2 G T U :
  G ⊢ T ⟿ μ U ->
  exists S, T = μ S.
Proof.
  introv Hr. dependent induction Hr; eauto.
  inversions H. destruct_all. invert_repl.
  specialize (IHHr _ eq_refl). destruct_all. eexists. eauto.
Qed.

Lemma repl_comp_bnd': forall G T T',
    G ⊢ μ T ⟿ μ T' ->
    G ⊢ T ⟿ T'.
Proof.
  introv Hr. dependent induction Hr.
  - apply star_refl.
  - destruct H as [?[?[?[?[?[? Hr']]]]]].
    assert (exists V, b = μ V) as [V ->]. {
      inversions Hr'. eauto.
    }
    apply star_trans with (b:=V). apply star_one. econstructor. repeat eexists. apply H. inversion* H0.
    inversions Hr'. eauto. apply* IHHr.
Qed.

Lemma repl_comp_trm_rcd G a T S :
  G ⊢ typ_rcd { a ⦂ T } ⟿ S ->
  exists T', S = typ_rcd { a ⦂ T' } /\ G ⊢ T ⟿ T'.
Proof.
  intros Hr. dependent induction Hr.
  - repeat eexists; apply star_refl.
  - destruct H as [p[q[n[U[Hp[Hq Hr']]]]]].
    specialize (IHHr _ _ eq_refl) as [T' [-> Hrr]]. invert_repl.
    eexists; split; eauto. apply star_trans with (b:=T'); auto. apply star_one. econstructor; repeat eexists; eauto.
Qed.

Lemma repl_comp_trm_rcd' G a T S :
  G ⊢ S ⟿ typ_rcd { a ⦂ T } ->
  exists T', S = typ_rcd { a ⦂ T' } /\ G ⊢ T' ⟿ T .
Proof.
  intros Hr. dependent induction Hr.
  - repeat eexists; apply star_refl.
  - destruct H as [p[q[n[U[Hp[Hq Hr']]]]]]. invert_repl.
    specialize (IHHr _ _ eq_refl) as [T' [-> Hrr]].
    eexists; split; eauto. apply star_trans with (b:=T2); auto. apply star_one. econstructor; repeat eexists; eauto.
Qed.

Lemma repl_comp_typ_and1 G T U S :
  G ⊢ S ⟿ T ∧ U ->
  exists T' U', S = T' ∧ U' /\ G ⊢ T' ⟿ T /\ G ⊢ U' ⟿ U.
Proof.
  intros Hr. dependent induction Hr.
  - repeat eexists; apply star_refl.
  - destruct H as [p[q[n[V[Hp[Hq Hr']]]]]]. invert_repl;
    specialize (IHHr _ _ eq_refl) as [T' [U' [-> [Hr1 Hr2]]]];
    repeat eexists; eauto; apply star_trans with (b:=T2); auto; apply star_one; econstructor; repeat eexists; eauto.
Qed.

Lemma repl_comp_typ_and2 G T U S :
  G ⊢ T ∧ U ⟿ S ->
  exists T' U', S = T' ∧ U' /\ G ⊢ T ⟿ T' /\ G ⊢ U ⟿ U'.
Proof.
  intros Hr. dependent induction Hr.
  - repeat eexists; apply star_refl.
  - destruct H as [p[q[n[V[Hp[Hq Hr']]]]]].
    specialize (IHHr _ _ eq_refl) as [T' [U' [-> [Hr1 Hr2]]]]; invert_repl; repeat eexists; eauto;
      [ apply star_trans with (b:=T') | apply star_trans with (b:=U') ];
      auto; apply star_one; econstructor; repeat eexists; eauto.
Qed.

Lemma repl_comp_record_has2 G T U U' a :
  G ⊢ T ⟿ U ->
  record_has U { a ⦂ U' } ->
  exists T', record_has T { a ⦂ T' } /\ G ⊢ T' ⟿ U'.
Proof.
  intros Hrc Hr. gen T. dependent induction Hr; introv Hrc.
  - apply repl_comp_trm_rcd' in Hrc as [T' [-> Hr]]. eauto.
  - apply repl_comp_typ_and1 in Hrc as [T' [U'' [-> [Hrc1 Hrc2]]]].
    specialize (IHHr _ _ eq_refl _ Hrc1) as [V [Hr' Hrc]].
    eexists. split. apply rh_andl. eauto. auto.
  - apply repl_comp_typ_and1 in Hrc as [T' [U'' [-> [Hrc1 Hrc2]]]].
    specialize (IHHr _ _ eq_refl _ Hrc2) as [V [Hr' Hrc]].
    eexists. split. apply rh_andr. eauto. auto.
Qed.

Lemma repl_comp_record_has1 G T U T' a :
  G ⊢ T ⟿ U ->
  record_has T { a ⦂ T' } ->
  exists U', record_has U { a ⦂ U' } /\ G ⊢ T' ⟿ U'.
Proof.
  intros Hrc Hr. gen U. dependent induction Hr; introv Hrc.
  - apply repl_comp_trm_rcd in Hrc as [T'' [-> Hr]]. eauto.
  - apply repl_comp_typ_and2 in Hrc as [T'' [U'' [-> [Hrc1 Hrc2]]]].
    specialize (IHHr _ _ eq_refl _ Hrc1) as [V [Hr' Hrc]].
    eexists. split. apply rh_andl. eauto. auto.
  - apply repl_comp_typ_and2 in Hrc as [T'' [U'' [-> [Hrc1 Hrc2]]]].
    specialize (IHHr _ _ eq_refl _ Hrc2) as [V [Hr' Hrc]].
    eexists. split. apply rh_andr. eauto. auto.
Qed.

Lemma repl_composition_open G T U p :
  inert G ->
  G ⊢ T ⟿ U ->
  G ⊢ open_typ_p p T ⟿ open_typ_p p U.
Proof.
  intros Hi Hrc. dependent induction Hrc.
  - apply star_refl.
  - eapply star_trans with (b:=open_typ_p p b); auto.
    destruct H as [q [r [n [V [Hp [Hq Hr]]]]]]. apply star_one. econstructor. repeat eexists.
    apply Hp. eauto. apply* repl_open.
    apply precise_to_general2 in Hq. apply* typed_paths_named.
    apply precise_to_general in Hp. apply* typed_paths_named.
Qed.

Lemma repl_composition_weaken_one G x T U V :
  ok G ->
  x # G ->
  G ⊢ T ⟿ U ->
  G & x ~ V ⊢ T ⟿ U.
Proof.
  intros Hok Hn Hr. gen x V. dependent induction Hr; intros.
  - constructor.
  - destruct H as [r [? [n [? [Hrq [? Hr']]]]]].
    eapply star_trans. apply star_one. econstructor. repeat eexists. apply* pf_weaken. apply* pt2_weaken.
    apply Hr'. apply* IHHr.
Qed.

Lemma repl_composition_weaken G G' T U :
  ok (G & G') ->
  G ⊢ T ⟿ U ->
  G & G' ⊢ T ⟿ U.
Proof.
  intros Hok Hr. induction G' using env_ind.
  - rewrite* concat_empty_r.
  - rewrite concat_assoc in *. apply ok_push_inv in Hok as [? ?].
    eapply repl_composition_weaken_one; eauto.
Qed.

Notation "G '⊩' T '⟿' U '⬳' V" := (G ⊢ T ⟿ U /\ G ⊢ V ⟿ U) (at level 40, T at level 59).
Notation "G '⊩' p '⟿'' q '⬳' r" := (G ⊢ p ⟿' q /\ G ⊢ r ⟿' q) (at level 40, p at level 59).

Lemma repl_comp_trans_open G S W T p :
  inert G ->
  G ⊩ S ⟿ W ⬳ T ->
  G ⊩ open_typ_p p S ⟿ open_typ_p p W ⬳ open_typ_p p T.
Proof.
  split; apply* repl_composition_open.
Qed.

Lemma repl_comp_trans_record_has G T S U V a :
  G ⊩ T ⟿ S ⬳ U ->
  record_has U {a ⦂ V} ->
  exists V' S', record_has T {a ⦂ V'} /\ G ⊩ V' ⟿ S' ⬳ V.
Proof.
  intros [Hc1 Hc2] Hr. pose proof (repl_comp_record_has1 Hc2 Hr) as [V1 [Hr1 Hc1']].
  pose proof (repl_comp_record_has2 Hc1 Hr1) as [V2 [Hr2 Hc2']]. repeat eexists; eauto.
Qed.

Lemma field_typing_comp1: forall G r q a U,
  inert G ->
  G ⊢ q ⟿' r ->
  G ⊢!!! q•a : U ->
  exists T, G ⊢!!! r•a : T.
Proof.
  introv Hi Hr Hq. gen a U. dependent induction Hr; introv Hq; eauto.
  destruct (repl_comp_sngl_inv1 Hr) as [p Heq]. subst.
  destruct H as [p' [q' [n [V [Hp' [Hq' Hr']]]]]].
  specialize (IHHr _ _ Hi eq_refl eq_refl _ _ Hq). destruct IHHr as [T Hpa].
  assert (G ⊢!!! p : {{ r }}) as Hpr. {
    clear Hq Hr. inversions Hr'. gen p' a T. induction bs; introv Hpa; introv Hq.
    repeat rewrite field_sel_nil in *. eauto.
    destruct (pt3_backtrack _ _ Hq) as [T1 Ht1]. rewrite proj_rewrite' in *.
    apply pt3_backtrack in Hq. destruct_all. rewrite proj_rewrite'.
    apply* pt3_field_elim_p.
  }
  apply* field_elim_q3.
Qed.

Lemma field_typing_comp2: forall G r q a U,
  inert G ->
  G ⊢ r ⟿' q ->
  G ⊢!!! q•a : U ->
  exists T, G ⊢!!! r•a : T.
Proof.
  introv Hi Hr Hq. gen a U. dependent induction Hr; introv Hqa; eauto. inversions H.
  rename x into p.
  destruct H0 as [q' [n [V [Hp [Hq Hr']]]]].
  assert (exists q', b = {{ q' }}) as [q'' Heq] by inversion* Hr'.
  subst. specialize (IHHr _ _ Hi eq_refl eq_refl). invert_repl. apply* IHHr. clear IHHr Hr.
  gen q' a U. induction bs; intros; simpls.
  - repeat rewrite field_sel_nil in *. apply* pt3_trans2.
  - rewrite <- proj_rewrite' in *. apply* pt3_field_trans'.
Qed.

Lemma repl_composition_fld_elim: forall G p q a T,
    inert G ->
    G ⊢ p ⟿' q ->
    G ⊢!!! p • a : T ->
    G ⊢ p•a ⟿' q•a.
Proof.
  introv Hi Hr. gen T. dependent induction Hr; introv Hpa.
  - apply star_refl.
  - assert (exists p', b = {{ p' }}) as [p' Heq]. {
      dependent induction H; destruct_all; eauto. inversions H1. eauto.
    } subst.
    specialize (IHHr _ _ Hi eq_refl eq_refl).
    destruct H as [p'' [q' [n [S [Hpq [Hq Hr']]]]]]. apply star_trans with (b:={{ p'•a }}).
    * apply star_one. inversions Hr'. repeat eexists; eauto.
      repeat rewrite <- proj_rewrite' in *.
      apply* rsngl.
    * invert_repl. apply* IHHr.
Qed.
