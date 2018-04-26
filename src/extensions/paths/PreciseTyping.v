(** printing |-#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing |-##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing |-##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing |-!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import Sequences.
Require Import Coq.Program.Equality List.
Require Import Definitions Binding RecordAndInertTypes Replacement Subenvironments Narrowing.
Require Export PreciseFlow.

Inductive precise_typing2: ctx -> path -> typ -> Prop :=
| pt2: forall G p T U,
    G ⊢! p : T ⪼ U ->
    G ⊢!! p: U
| pt2_sngl_trans : forall G p q a U,
    G ⊢!! p : typ_sngl q ->
    G ⊢!! q•a : U ->
    G ⊢!! p•a : typ_sngl q•a
where "G '⊢!!' p ':' T" := (precise_typing2 G p T).

Inductive precise_typing3: ctx -> path -> typ -> Prop :=
| pt3: forall G p T,
    G ⊢!! p : T ->
    G ⊢!!! p: T
| pt3_sngl_trans : forall G p q T,
    G ⊢!! p : typ_sngl q ->
    G ⊢!!! q : T ->
    G ⊢!!! p : T
where "G '⊢!!!' p ':' T" := (precise_typing3 G p T).

Hint Constructors precise_typing2 precise_typing3.

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

Lemma pf2_and_destruct1: forall G p T U,
    G ⊢!! p: typ_and T U ->
    G ⊢!! p: T.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

Lemma pf2_and_destruct2: forall G p T U,
    G ⊢!! p: typ_and T U ->
    G ⊢!! p: U.
Proof.
  introv Hp. dependent induction Hp; eauto.
Qed.

Lemma pf3_and_destruct1: forall G p T U,
    G ⊢!!! p: typ_and T U ->
    G ⊢!!! p: T.
Proof.
  introv Hp. dependent induction Hp; eauto. constructor.
  apply* pf2_and_destruct1.
Qed.

Lemma pf3_and_destruct2: forall G p T U,
    G ⊢!!! p: typ_and T U ->
    G ⊢!!! p: U.
Proof.
  introv Hp. dependent induction Hp; eauto. constructor.
  apply* pf2_and_destruct2.
Qed.

Lemma pf2_inertsngl : forall G p T,
    inert G ->
    G ⊢!! p: T ->
    inert_sngl T \/ record_type T.
Proof.
  introv Hi Pf. induction Pf.
  - apply* pf_inertsngl.
  - left. right. eexists. eauto.
Qed.

Lemma pf3_inertsngl : forall G p T,
    inert G ->
    G ⊢!!! p: T ->
    inert_sngl T \/ record_type T.
Proof.
  introv Hi Pf. induction Pf; eauto;
  apply* pf2_inertsngl.
Qed.

Lemma pf2_bot: forall G p,
    inert G ->
    G ⊢!! p: typ_bot -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto using pf_bot.
Qed.

Lemma pf3_bot: forall G p,
    inert G ->
    G ⊢!!! p: typ_bot -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto using pf2_bot.
Qed.

Lemma pt2_psel: forall G p q A,
    inert G ->
    G ⊢!! p : typ_path q A -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pf_psel.
Qed.

Lemma pt3_psel: forall G p q A,
    inert G ->
    G ⊢!!! p : typ_path q A -> False.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. apply* pt2_psel.
Qed.

Lemma pt3_trans: forall G p q a U,
    G ⊢!! p : typ_sngl q ->
    G ⊢!!! q•a : U ->
    G ⊢!!! p•a : U.
Proof.
  introv Hp Hq. gen p. dependent induction Hq; introv Hp; eauto.
Qed.

Lemma pt3_trans2: forall G p q a U,
    G ⊢!!! p : typ_sngl q ->
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
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! q•a : T ->
    G ⊢!!! p•a : typ_sngl q•a.
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
  - destruct (pf_path_sel _ _ Hi Hp1) as [V [W Hp]].
    lets Hpa: (pf_fld Hp). lets Heq: (pf_T_unique Hi Hp1 Hpa). subst.
    assert (inert_sngl (typ_sngl q)) as His'. { right. eexists. auto. }
    specialize (IHHp2_1 Hi His' _ _ Hp). inversion IHHp2_1.
Qed.

Lemma pf_pt2_sngl: forall G p T U q,
    inert G ->
    G ⊢! p: T ⪼ U ->
    G ⊢!! p: typ_sngl q ->
    T = typ_sngl q.
Proof.
  introv Hi Hp1 Hp2. apply* pf_pt2. right. eexists. auto.
Qed.

Lemma field_elim_q0: forall G p q a T,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
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
    G ⊢!! p: typ_sngl q ->
    G ⊢! p•a : T ⪼ T' ->
    exists U, G ⊢!! q•a: U.
Proof.
  introv Hi Hp Hpa. gen q.
  dependent induction Hpa; introv Hp; try simpl_dot; eauto.
  lets Hp2: (pf_pt2_sngl Hi Hpa Hp). subst.
  apply pf_sngl_U in Hpa. inversion Hpa.
Qed.

Lemma pt2_unique: forall G p T1 T2,
    inert G ->
    G ⊢!! p: T1 ->
    G ⊢!! p: T2 ->
    inert_sngl T1 ->
    T1 = T2.
Proof.
  introv Hi Hp1 Hp2 His1. gen T2. dependent induction Hp1; introv Hp2.
  - dependent induction Hp2.
    * lets HU: (pf_T_unique Hi H H0). subst.
      admit. (*easy*)
    * lets Hp: (pt2_sngl_trans _ Hp2_1 Hp2_2).
      lets Heq: (pf_pt2_sngl Hi H Hp). subst.
      apply* pf_sngl_U.
  - assert (inert_sngl (typ_sngl q)) as His. { right. eexists. auto. }
    clear His1 His.
    gen q U. dependent induction Hp2; introv Hp1 IH1 Hqa IH2; eauto.
    * lets Hp: (pt2_sngl_trans _ Hp1 Hqa).
      lets Heq: (pf_pt2_sngl Hi H Hp). subst. lets Heq: (pf_sngl_U H). auto.
    * simpl_dot.
      assert (inert_sngl (typ_sngl q0)) as His. { right. eexists. auto. }
      assert (inert_sngl (typ_sngl q)) as His'. { right. eexists. auto. }
      specialize (IH1 Hi His _ Hp2_1). inversion* IH1.
Qed.

Lemma field_elim_q: forall G p q a T,
    inert G ->
    G ⊢!! p: typ_sngl q ->
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
      assert (inert_sngl (typ_sngl q)) as His. {
        right. eexists. eauto.
      }
      assert (inert_sngl (typ_sngl q0•a)) as His'. {
        right. eexists. eauto.
      }
      lets Hu: (pt2_unique Hi Hpa1 Hxbs His).
      inversions Hu. eauto.
Qed.

Lemma field_elim_q2: forall G p q a T,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
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
    G ⊢!!! p: typ_sngl q ->
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
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! p • a : U ->
    G ⊢!!! p • a : typ_sngl q • a.
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
    G ⊢!!! p: typ_sngl q ->
    G ⊢!!! q: T ->
    G ⊢!!! p : T.
Proof.
  introv Hp Hq. gen T. dependent induction Hp; introv Hq; eauto.
Qed.

Lemma pt3_field_trans: forall G p q bs T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! q••bs : T ->
    G ⊢!!! p••bs : typ_sngl q••bs.
Proof.
  introv Hi Hp Hq. gen T q. induction bs; introv Hp Hq;
                              unfolds sel_fields; destruct q, p; simpls; auto.
  rewrite proj_rewrite in *.
  destruct (pt3_backtrack _ _ Hq) as [U Hb].
  specialize (IHbs _ _ Hp Hb). rewrite proj_rewrite. apply* path_elim_prec.
Qed.

Lemma pt3_field_trans': forall G p q bs T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
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

Lemma sngl_typed : forall G p q,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    exists T, G ⊢! q: T ⪼ T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto; try solve [apply pf_sngl_U in Hp; inversion Hp].
  - apply binds_inert in H0. inversion H0. auto.
  - destruct (pf_bnd_T2 Hi Hp) as [U Heq]. subst. destruct (pf_rec_rcd_U Hi Hp).
    * inversion H.
    * inversions H. inversions H0. admit.
      (* here we change the def of inertness and get what we want? *)
Qed.

Lemma sngl_typed2 : forall G p q,
    inert G ->
    G ⊢!! p: typ_sngl q ->
    exists T, G ⊢!! q: T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto. lets Heq: (pf_sngl_T Hi H). subst.
  destruct* (sngl_typed Hi H).
Qed.

Lemma sngl_typed3 : forall G p q,
    inert G ->
    G ⊢!!! p: typ_sngl q ->
    exists T, G ⊢!!! q: T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
  destruct* (sngl_typed2 Hi H).
Qed.

Lemma pt3_trans_trans: forall G p q bs T,
    inert G ->
    G ⊢!!! p : typ_sngl q ->
    G ⊢!!! p••bs : T ->
    G ⊢!!! p••bs : typ_sngl q••bs.
Proof.
  introv Hi Hp Hpbs. gen p q T.
  induction bs; introv Hp; introv Hpbs; unfolds sel_fields; destruct p, q; simpls; auto.
  repeat rewrite proj_rewrite in *. apply* pt3_field_elim_p.
  specialize (IHbs _ _ Hp). apply pt3_backtrack in Hpbs. destruct_all. eauto.
Qed.

Lemma pf_sngl_fld_elim: forall G p q a T U,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢! p•a : T ⪼ U ->
    False.
Proof.
  introv Hi Hp Hpa. dependent induction Hpa; try simpl_dot; eauto.
  lets Hu: (pf_T_unique Hi Hpa Hp). subst. apply pf_sngl_U in Hpa. false*.
Qed.

Lemma pf_sngl_flds_elim: forall G p q T U bs,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
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
    G ⊢!! p: typ_bnd T ->
    G ⊢!! p: open_typ_p p T.
Proof.
  introv Hi Hp. dependent induction Hp; eauto.
Qed.

Lemma pt3_bnd : forall G p T,
    inert G ->
    G ⊢!!! p: typ_bnd T ->
    G ⊢!!! p: open_typ_p p T \/
              (exists q, G ⊢!!! p: typ_sngl q /\ G ⊢!!! p: open_typ_p q T).
Proof.
  introv Hi Hp. dependent induction Hp.
  - left. constructor. apply* pt2_bnd.
  - specialize (IHHp _ Hi eq_refl). destruct IHHp as [Hq | [r [Hr1 Hr2]]]; right*.
Qed.

Lemma pt2_exists: forall G p T,
    G ⊢!!! p: T ->
    exists U, G ⊢!! p: U.
Proof.
  induction 1; eauto.
Qed.

Lemma pf_pt2_trans_inv_mult : forall G p q bs T,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
    G ⊢!! p •• bs : T ->
    T = typ_sngl q •• bs.
Proof.
  introv Hi Hp Hpbs. gen T. induction bs; introv Hpbs.
  - repeat rewrite field_sel_nil in *. apply pt2 in Hp. apply eq_sym.
    apply* pt2_unique. right. eexists. eauto.
  - rewrite proj_rewrite' in *. destruct (pt2_backtrack _ _ Hpbs) as [U Hb].
    apply pt2 in Hp. specialize (IHbs _ Hb). subst.
    destruct (field_elim_q _ Hi Hb Hpbs) as [U Hf].
    lets Hp2: (pt2_sngl_trans _ Hb Hf). apply eq_sym. apply (pt2_unique Hi Hp2 Hpbs).
    right. eexists. eauto.
Qed.

Lemma pf_pt3_trans_inv_mult : forall G p q T,
    inert G ->
    G ⊢!! p: typ_sngl q ->
    G ⊢!!! p : T ->
    inert_typ T \/ record_type T ->
    G ⊢!!! q : T.
Proof.
  introv Hi Hpq Hp Hr. gen q. induction Hp; introv Hpq.
  - constructor.
    assert (inert_sngl (typ_sngl q)) as His. {
      right. eexists. eauto.
    }
    lets Hu: (pt2_unique Hi Hpq H His). subst. destruct Hr.
    inversion His. inversion H1. inversion H0. inversion H0. inversion H1.
  - specialize (IHHp Hi Hr).
    assert (inert_sngl (typ_sngl q)) as His1. {
      right. eexists. eauto.
    }
    assert (inert_sngl (typ_sngl q0)) as His2. {
      right. eexists. eauto.
    }
    lets Hu: (pt2_unique Hi Hpq H His2). inversions Hu. eauto.
Qed.

Lemma pf_pt3_trans_inv_mult' : forall G p q T bs,
    inert G ->
    G ⊢! p: typ_sngl q ⪼ typ_sngl q ->
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
  - clear IHHp3. apply pt2 in Hp1. assert (inert_sngl (typ_sngl q)) as His. {
      right. eexists. eauto.
    }
    lets Hu: (pt2_unique Hi H Hp1 His). inversion Hu.
Qed.

(** Lemmas about replacement composition *)

Definition typed_repl_comp_qp G T1 T2 :=
  exists p q n,
    G ⊢! p: typ_sngl q ⪼ typ_sngl q /\ repl_typ n q p T1 T2.

Definition repl_composition_qp G := star (typed_repl_comp_qp G).

Lemma repl_comp_sngl_inv1 : forall G T p,
    repl_composition_qp G T (typ_sngl p) ->
    exists q, T = typ_sngl q.
Proof.
  introv Hr. dependent induction Hr; eauto.
  specialize (IHHr _ eq_refl). destruct_all. subst.
  inversions H. destruct_all. invert_repl. eexists; eauto.
Qed.

Lemma repl_comp_sngl_inv2 : forall G T p,
    repl_composition_qp G (typ_sngl p) T ->
    exists q, T = typ_sngl q.
Proof.
  introv Hr. dependent induction Hr; eauto.
  inversions H. destruct_all. invert_repl.
  specialize (IHHr _ eq_refl). destruct_all. eexists. eauto.
Qed.

Lemma repl_comp_and1: forall G T T' U,
    repl_composition_qp G T T' ->
    repl_composition_qp G (typ_and T U) (typ_and T' U).
Proof.
  introv Hr. dependent induction Hr.
  - apply star_refl.
  - apply star_trans with (b:=typ_and b U); auto. apply star_one.
    unfolds typed_repl_comp_qp. destruct_all.
    repeat eexists; eauto.
Qed.

Lemma repl_comp_and2: forall G T T' U,
    repl_composition_qp G T T' ->
    repl_composition_qp G (typ_and U T) (typ_and U T').
Proof.
  introv Hr. dependent induction Hr.
  - apply star_refl.
  - apply star_trans with (b:=typ_and U b); auto. apply star_one.
    unfolds typed_repl_comp_qp. destruct_all.
    repeat eexists; eauto.
Qed.

Lemma repl_composition_sngl: forall G p q T,
    inert G ->
    repl_composition_qp G (typ_sngl q) (typ_sngl p) ->
    G ⊢!!! p : T ->
    p = q \/ G ⊢!!! p : typ_sngl q.
Proof.
  introv Hi Hc Hq. dependent induction Hc; eauto.
  assert (exists r, b = typ_sngl r) as [p3 Heq] by admit. subst.
  specialize (IHHc _ _ Hi eq_refl eq_refl Hq).
  destruct H as [r1 [r2 [n [H Hr]]]]. inversions Hr.
  lets H': (pt3 (pt2 H)).
  destruct IHHc as [Heq | Hp]; subst.
  - lets Htt: (pt3_trans_trans _ Hi H' Hq).
    right*.
  - right.
    destruct (sngl_typed3 Hi Hp) as [S Hqbs].
    lets Htt: (pt3_trans_trans _ Hi H' Hqbs). apply* pt3_sngl_trans3.
Qed.

Lemma repl_composition_sngl2: forall G p q T,
    inert G ->
    repl_composition_qp G (typ_sngl q) (typ_sngl p) ->
    G ⊢!!! q : T ->
    p = q \/ G ⊢!!! p : typ_sngl q.
Proof.
  introv Hi Hc Hq. gen T. dependent induction Hc; introv Hq; eauto.
  assert (exists r, b = typ_sngl r) as [p3 Heq] by admit. subst.
  specialize (IHHc _ _ Hi eq_refl eq_refl).
  destruct H as [r1 [r2 [n [H Hr]]]]. inversions Hr.
  lets H': (pt3 (pt2 H)).
  lets Hqs: (pt3_field_trans _ Hi H' Hq).
  destruct (IHHc _ Hqs) as [Heq | Hp]; subst.
  - lets Htt: (pt3_trans_trans _ Hi H' Hqs). right*.
  - right. destruct (sngl_typed3 Hi Hp) as [S' Hqbs].
    lets Htt: (pt3_trans_trans _ Hi H' Hqbs). apply* pt3_sngl_trans3.
Qed.

Lemma field_typing_comp1: forall G r q a U,
  inert G ->
  repl_composition_qp G (typ_sngl r) (typ_sngl q) ->
  G ⊢!!! q•a : U ->
  exists T, G ⊢!!! r•a : T.
Proof.
  introv Hi Hr Hq. gen a U. dependent induction Hr; introv Hq; eauto.
  destruct (repl_comp_sngl_inv1 Hr) as [p Heq]. subst.
  destruct H as [p' [q' [n [Hp' Hr']]]].
  specialize (IHHr _ _ Hi eq_refl eq_refl _ _ Hq). destruct IHHr as [T Hpa].
  assert (G ⊢!!! p : typ_sngl r) as Hpr. {
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
  repl_composition_qp G (typ_sngl q) (typ_sngl r) ->
  G ⊢!!! q•a : U ->
  exists T, G ⊢!!! r•a : T.
Proof.
  introv Hi Hr Hq. gen a U. dependent induction Hr; introv Hqa; eauto. inversions H.
  rename x into p.
  destruct H0 as [q' [n [Hp Hr']]].
  assert (exists q', b = typ_sngl q') as [q'' Heq] by inversion* Hr'.
  subst. specialize (IHHr _ _ Hi eq_refl eq_refl). invert_repl. apply* IHHr. clear IHHr Hr.
  gen q' a U. induction bs; intros; simpls.
  - repeat rewrite field_sel_nil in *. apply* pt3_trans2.
  - rewrite <- proj_rewrite' in *. apply* pt3_field_trans'.
Qed.

Lemma repl_composition_fld_elim: forall G p q a T,
    inert G ->
    repl_composition_qp G (typ_sngl p) (typ_sngl q) ->
    G ⊢!!! p • a : T ->
    repl_composition_qp G (typ_sngl p•a) (typ_sngl q•a).
Proof.
  introv Hi Hr. gen T. dependent induction Hr; introv Hpa.
  - apply star_refl.
  - assert (exists p', b = typ_sngl p') as [p' Heq]. {
      dependent induction H; destruct_all; eauto. inversions H0. eauto.
    } subst.
    specialize (IHHr _ _ Hi eq_refl eq_refl).
    destruct H as [p'' [q' [n [Hpq Hr']]]]. apply star_trans with (b:=typ_sngl p' • a).
    * apply star_one. inversions Hr'. repeat eexists. apply Hpq.
      repeat rewrite <- proj_rewrite' in *.
      apply* rsngl.
    * invert_repl. apply* IHHr. clear IHHr. rewrite <- proj_rewrite' in *.
      apply* pt3_field_trans'.
Qed.

Lemma repl_comp_to_prec: forall G p q T,
    inert G ->
    repl_composition_qp G (typ_sngl q) (typ_sngl p) ->
    G ⊢!!! p: T ->
    p = q \/ G ⊢!!! p: typ_sngl q.
Proof.
  introv Hi Hr Hp. gen T. dependent induction Hr; introv Hp; eauto.
  assert (exists r, b = typ_sngl r) as [r Heq] by admit. subst.
  specialize (IHHr _ _ Hi eq_refl eq_refl). destruct (IHHr _ Hp). subst.
  - destruct H as [p1 [p2 [n [H1 H2]]]]. right. inversions H2.
    repeat rewrite proj_rewrite_mult in *.
    destruct (pt2_exists Hp) as [U Hu].
    lets Hpf: (pf_pt2_trans_inv_mult _ Hi H1 Hu). subst*.
  - specialize (IHHr _ Hp). destruct H as [p1 [p2 [n [H1 H2]]]].
    destruct (repl_prefixes_sngl H2) as [bs [He1 He2]]. subst.
    destruct IHHr as [Heq | IH].
    * subst. right. lets Hs: (sngl_typed3 Hi (pt3 (pt2 H1))). destruct Hs.
      apply* pt3_trans_trans.
    * right*. apply* pt3_sngl_trans3.
      lets Hs: (sngl_typed3 Hi IH). destruct Hs.
      apply* pt3_trans_trans.
 Qed. (* todo: rewrite above lemmas using this lemma *)
